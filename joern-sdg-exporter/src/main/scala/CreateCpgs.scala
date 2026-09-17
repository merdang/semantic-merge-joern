import io.joern.javasrc2cpg.{Config, JavaSrc2Cpg}
import io.joern.x2cpg.X2Cpg
import io.joern.dataflowengineoss.layers.dataflows.{OssDataFlow, OssDataFlowOptions}
import io.shiftleft.codepropertygraph.generated.{Cpg, EdgeTypes, Properties}
import io.shiftleft.codepropertygraph.generated.nodes.{StoredNode, AstNode, Method, Call}
import io.shiftleft.codepropertygraph.generated.edges.ReachingDef
import io.shiftleft.semanticcpg.language.*
import io.shiftleft.semanticcpg.layers.LayerCreatorContext

import java.nio.file.{Files, Paths}
import scala.jdk.CollectionConverters.*
import scala.util.{Failure, Success}
import scala.collection.mutable

object CreateCpgs:

  // The examples tree. Relative to the exporter's working directory by default
  // (sbt runs with user.dir at the sbt project root, one level under the repo
  // root); set SDG_EXAMPLES_DIR to export a tree that lives somewhere else.
  val baseDir =
    Paths.get(sys.env.getOrElse("SDG_EXAMPLES_DIR", "../examples"))
      .toAbsolutePath.normalize.toString

  val targets = List(
    ("base.java", "base"),
    ("a.java",    "a"),
    ("b.java",    "b")
  )

  // ── JSON helpers ─────────────────────────────────────────────────────────────
  private def esc(s: String): String =
    val b = new StringBuilder
    s.foreach {
      case '"'  => b ++= "\\\""
      case '\\' => b ++= "\\\\"
      case '\n' => b ++= "\\n"
      case '\r' => b ++= "\\r"
      case '\t' => b ++= "\\t"
      case c if c.isControl => b ++= f"\\u${c.toInt}%04x"
      case c    => b += c
    }
    b.toString

  private def jStr(s: String): String = "\"" + esc(s) + "\""

  private def optToJson(o: Option[?]): String = o match
    case Some(i: Integer) => i.intValue.toString
    case Some(i: Int)     => i.toString
    case Some(v)          => jStr(v.toString)
    case None             => "null"

  // ── statement-level PDG vertices, mirroring joern-export --repr pdg ──────────
  private val statementLabels = Set(
    "METHOD", "METHOD_PARAMETER_IN", "METHOD_RETURN",
    "CALL", "RETURN", "CONTROL_STRUCTURE"
  )

  private def isStatementVertex(n: StoredNode): Boolean =
    statementLabels.contains(n.label)

  // Joern chains REACHING_DEF through sub-expressions across statements —
  // value availability, not def-use — which at statement granularity would
  // manufacture dependences between unrelated statements. A cross-statement
  // DDG source must therefore be a definition carrier: a whole statement, a
  // parameter, a return, or an assignment/increment sub-expression.
  private val assignmentOps = Set(
    "<operator>.assignment", "<operator>.assignmentPlus", "<operator>.assignmentMinus",
    "<operator>.assignmentMultiplication", "<operator>.assignmentDivision",
    "<operator>.preIncrement", "<operator>.postIncrement",
    "<operator>.preDecrement", "<operator>.postDecrement"
  )

  // Receivers whose REACHING_DEF chain we keep as an *ordering* dependence
  // rather than discard as value availability — see the output-ordering pass.
  private val streamReceivers = Set("System.out", "System.err")

  // Loop headers, for the loop-carriage test (HPR §4.1).
  private val loopKeywords = Set("while", "for", "do")

  // Is this vertex a *statement* rather than a sub-expression? A statement's
  // AST parent is the enclosing BLOCK, while `a + 2` inside `a = a + 2` hangs
  // off its operator. Exported rather than inferred from source spans, which
  // is unsafe in G_M where vertices from different versions share coordinates.
  private def isBlockChild(n: StoredNode): Boolean =
    n match
      case a: AstNode =>
        a.astParent match
          case p: StoredNode => p.label == "BLOCK"
          case _             => false
      case _ => false

  private def isDefCarrier(n: StoredNode): Boolean =
    n.label == "METHOD" || n.label == "METHOD_PARAMETER_IN" || n.label == "RETURN"
      || assignmentOps.contains(n.property(Properties.Name))
      || isBlockChild(n)

  // Variables a statement *writes*, read off the AST rather than off
  // REACHING_DEF: a dead definition has no outgoing reaching-def edge, so it
  // is invisible in the edge set, and feasibility's kill-order reasoning still
  // has to see it.
  // Variables a statement *declares*. Java requires declaration before use and
  // a PDG cannot express that, so a scheduler free to reorder would otherwise
  // push a declaration past its uses. A LOCAL sharing the statement's line is
  // that statement's declaration.
  private def declaredVars(n: StoredNode, localsByLine: Map[Int, Set[String]]): List[String] =
    n.property(Properties.LineNumber) match
      case Some(line) =>
        val here = localsByLine.getOrElse(line, Set.empty)
        definedVars(n).filter(here.contains)
      case _ => Nil

  private def definedVars(n: StoredNode): List[String] =
    val out = mutable.LinkedHashSet.empty[String]
    if n.label == "METHOD_PARAMETER_IN" then out += n.property(Properties.Name)
    val subtree: List[AstNode] = n match
      // The entry vertex writes nothing of its own: its AST subtree is the
      // entire body, which would make it a universal writer. Parameters are
      // separate vertices and carry their own names.
      case a: AstNode if a.label == "METHOD" => Nil
      // A control structure writes only what its *condition* writes — the
      // guarded body's statements are separate vertices carrying their own
      // definitions. Same subtree rule as its DDG in-edges; taking the
      // whole subtree would make the header a universal writer.
      case a: AstNode if a.label == "CONTROL_STRUCTURE" =>
        a.astChildren.filter(_.label != "BLOCK").flatMap(_.ast).l
      case a: AstNode => a.ast.l
      case _          => Nil
    subtree.foreach { c =>
      if assignmentOps.contains(c.property(Properties.Name)) then
        // the assignment target is the operator's first AST child
        c.astChildren.l.headOption.foreach { lhs =>
          if lhs.label == "IDENTIFIER" then out += lhs.property(Properties.Name)
        }
    }
    out.toList

  // ── per-version export ───────────────────────────────────────────────────────
  private def exportCpg(cpg: Cpg, version: String, outPath: String): Unit =
    def vid(n: StoredNode, methodFullName: String): String =
      s"$version::$methodFullName::n${n.id()}"

    val methodsJson = mutable.ArrayBuffer.empty[String]

    val internalMethods = cpg.method.isExternal(false).filter(_.cfgNode.nonEmpty).l

    internalMethods.foreach { m =>
      val mfn = m.fullName

      val header   : List[StoredNode] = List(m)
      val params   : List[StoredNode] = m.parameter.l
      val ret      : List[StoredNode] = m.methodReturn :: Nil
      val body     : List[StoredNode] = m.cfgNode.filter(isStatementVertex).l
      val vertices : List[StoredNode] = (header ++ params ++ ret ++ body).distinctBy(_.id())

      val idOf: Map[Long, String] = vertices.map(n => n.id() -> vid(n, mfn)).toMap

      // locals grouped by declaration line, for `declares` below
      val localsByLine: Map[Int, Set[String]] =
        m.local.l
          .flatMap(l => l.property(Properties.LineNumber).map(_.toInt -> l.name))
          .groupMap(_._1)(_._2)
          .view.mapValues(_.toSet).toMap

      // ── nodes ────────────────────────────────────────────────────────────────
      val nodesJson = vertices.map { n =>
        val nm = n.property(Properties.Name)
        val fields = List(
          s"\"id\": ${jStr(idOf(n.id()))}",
          s"\"label\": ${jStr(n.label)}",
          s"\"code\": ${jStr(n.property(Properties.Code))}",
          s"\"name\": ${if nm.isEmpty then "null" else jStr(nm)}",
          s"\"lineNumber\": ${optToJson(n.property(Properties.LineNumber))}",
          s"\"columnNumber\": ${optToJson(n.property(Properties.ColumnNumber))}",
          s"\"lineNumberEnd\": ${optToJson(n.property(Properties.LineNumberEnd))}",
          s"\"columnNumberEnd\": ${optToJson(n.property(Properties.ColumnNumberEnd))}",
          s"\"defs\": [${definedVars(n).map(jStr).mkString(", ")}]",
          s"\"declares\": [${declaredVars(n, localsByLine).map(jStr).mkString(", ")}]",
          s"\"statement\": ${isBlockChild(n)}"
        )
        "        { " + fields.mkString(", ") + " }"
      }


      // ── edges ────────────────────────────────────────────────────────────────
      val edgesJson = mutable.ArrayBuffer.empty[String]

      // climb the AST until we hit a vertex that's in our idOf set
      def enclosingStmt(n: StoredNode): Option[StoredNode] =
        if isStatementVertex(n) && idOf.contains(n.id()) then Some(n)
        else
          var cur: Option[StoredNode] = Some(n)
          var found: Option[StoredNode] = None
          var steps = 0
          while cur.isDefined && found.isEmpty && steps < 64 do
            cur = cur.get match
              case a: AstNode =>
                a.astParent match
                  case p: StoredNode => Some(p)
                  case _             => None
              case _ => None
            cur.foreach { p =>
              if idOf.contains(p.id()) then found = Some(p)
            }
            steps += 1
          found

      // climb to the statement that actually occupies a slot in a block. Unlike
      // enclosingStmt this walks *past* sub-expression vertices: those are in
      // idOf (they are CALLs) but are not statements, and ordering is a
      // statement-level question.
      def enclosingBlockStmt(n: StoredNode): Option[StoredNode] =
        var cur: Option[StoredNode] = Some(n)
        var found: Option[StoredNode] = None
        var steps = 0
        while cur.isDefined && found.isEmpty && steps < 64 do
          val c = cur.get
          val isBlockChild = c match
            case a: AstNode =>
              a.astParent match
                case p: StoredNode => p.label == "BLOCK"
                case _             => false
            case _ => false
          if idOf.contains(c.id()) && isBlockChild then found = Some(c)
          else
            cur = c match
              case a: AstNode =>
                a.astParent match
                  case p: StoredNode => Some(p)
                  case _             => None
              case _ => None
          steps += 1
        found

      // `astParent` throws NoSuchElementException at the AST root rather than
      // returning null, so every upward walk needs this guard — the existing
      // walks only avoid it by stopping at a known vertex first.
      def astParentOf(n: StoredNode): Option[StoredNode] =
        n match
          case a: AstNode =>
            scala.util.Try(a.astParent).toOption match
              case Some(p: StoredNode) => Some(p)
              case _                   => None
          case _ => None

      def posKey(n: StoredNode): (Int, Int, Long) =
        (n.property(Properties.LineNumber).map(_.toInt).getOrElse(-1),
         n.property(Properties.ColumnNumber).map(_.toInt).getOrElse(-1),
         n.id())

      // Loop carriage (HPR §4.1). A flow dependence is loop-CARRIED when the
      // value crosses the backedge, loop-INDEPENDENT when it flows within one
      // iteration, and the two order a block oppositely: independent puts the
      // definition first, carried puts it last. For the structured loops we
      // accept, source order decides it — a definition written after the use
      // can only reach it across the backedge.
      def enclosingLoopIds(n: StoredNode): Set[Long] =
        val out = mutable.Set.empty[Long]
        var cur = astParentOf(n)
        var steps = 0
        while cur.isDefined && steps < 64 do
          val c = cur.get
          if c.label == "CONTROL_STRUCTURE"
             && loopKeywords.exists(c.property(Properties.Code).trim.startsWith) then
            out += c.id()
          cur = astParentOf(c)
          steps += 1
        out.toSet

      def isLoopCarried(src: StoredNode, dst: StoredNode): Boolean =
        enclosingLoopIds(src).intersect(enclosingLoopIds(dst)).nonEmpty
          && summon[Ordering[(Int, Int, Long)]].gt(posKey(src), posKey(dst))

      // read the variable label off a REACHING_DEF edge via the typed edge class
      def varOf(e: flatgraph.Edge): String = e match
        case rd: ReachingDef =>
          rd.propertyMaybe match
            case Some(s: String) => s
            case _               => ""
        case _ => ""

      // A definition must reach *every* use, not just the first. Joern chains
      // REACHING_DEF through sub-expressions — for `int y = 1; int a = y + 1;
      // int b = y + 2;` it emits y=1 -> y+1 -> y+2 rather than an edge from the
      // definition to each use — and the def-carrier rule below keeps only the
      // first hop, because the source of the second is a sub-expression. Every
      // use after the first therefore lost its dependence on the definition
      // outright: backward slices came out too small, forward closures too
      // short, and interference could be missed — unsound, not merely
      // mis-ordered.
      //
      // So walk back through the chain rather than dropping the edge: from a
      // sub-expression source, follow REACHING_DEF in-edges on the same
      // variable until a real definition carrier is reached. A receiver chain
      // walks back to a field access no statement defines, finds no carrier,
      // and still yields nothing — value availability with no definition
      // behind it is not a dependence.
      def resolveCarriers(from: StoredNode, variable: String): List[StoredNode] =
        val found = mutable.LinkedHashMap.empty[Long, StoredNode]
        val seen  = mutable.Set.empty[Long]
        val work  = mutable.Queue.empty[StoredNode]
        work.enqueue(from)
        var steps = 0
        while work.nonEmpty && steps < 512 do
          steps += 1
          val cur = work.dequeue()
          if seen.add(cur.id()) then
            cur.inE(EdgeTypes.REACHING_DEF).foreach { e =>
              if varOf(e) == variable then
                val prev = e.src.asInstanceOf[StoredNode]
                enclosingStmt(prev) match
                  case Some(st) if isDefCarrier(st) => found.getOrElseUpdate(st.id(), st)
                  case _                            => work.enqueue(prev)
            }
        found.values.toList

      // DDG: walk REACHING_DEF edges into every node of each statement's subtree,
      // lift to enclosing statement, dedupe; drop METHOD-rooted empty-label noise.
      val seenDdg = mutable.Set.empty[(Long, Long, String, String, Long)]
      // (source, variable) -> statements that definition flows to. Def-order
      // clause (3) needs a component both definitions flow to; this is that
      // index, filled as the DDG is emitted.
      val ddgTargets = mutable.Map.empty[(Long, String), mutable.Set[Long]]

      def emitEdge(src: StoredNode, dst: StoredNode, variable: String, kind: String,
                   witness: Option[Long] = None): Unit =
        if src.id() == dst.id() then return
        val isMethodNoise = src.isInstanceOf[Method] && variable.isEmpty
        if isMethodNoise then return
        val key = (src.id(), dst.id(), variable, kind, witness.getOrElse(-1L))
        if seenDdg.contains(key) then return
        seenDdg += key
        if kind == "DDG" then
          ddgTargets.getOrElseUpdate((src.id(), variable), mutable.Set.empty) += dst.id()
        val varField = if variable.isEmpty then "" else s", \"variable\": ${jStr(variable)}"
        val witField = witness.map(w => s", \"witness\": ${jStr(idOf(w))}").getOrElse("")
        // carriage is a property of a flow dependence only
        val carField = if kind == "DDG" && isLoopCarried(src, dst) then ", \"carried\": true" else ""
        edgesJson += s"        { \"src\": ${jStr(idOf(src.id()))}, \"dst\": ${jStr(idOf(dst.id()))}, \"kind\": ${jStr(kind)}${varField}${witField}${carField} }"

      def emitDdgEdge(src: StoredNode, dst: StoredNode, variable: String): Unit =
        emitEdge(src, dst, variable, "DDG")

      // for each statement vertex in the body, look at REACHING_DEF in-edges on
      // the statement node itself plus every AST descendant
      body.foreach { dstStmt =>
        val subtree: List[StoredNode] = dstStmt match
          // A loop/if header's own dependences come from its CONDITION
          // only. Joern's REACHING_DEF reaches the header from every
          // definition in the body (the header is re-evaluated on each
          // iteration), so taking the header's *whole* AST subtree lifts every
          // body definition onto the header vertex and turns it into a
          // universal join point: every body statement becomes reachable from
          // every other, and two independent edits inside one loop falsely
          // interfere. Same failure mode as the METHOD_RETURN artifact.
          // The body's statements are separate PDG vertices carrying their own
          // dependences, so excluding the body BLOCK loses nothing.
          case a: AstNode if a.label == "CONTROL_STRUCTURE" =>
            dstStmt :: a.astChildren.filter(_.label != "BLOCK").flatMap(_.ast).l
          case a: AstNode => a.ast.l
          case _          => List(dstStmt)
        val subtreeIds = subtree.map(_.id()).toSet
        subtree.foreach { dstNode =>
          dstNode.inE(EdgeTypes.REACHING_DEF).foreach { e =>
            val src = e.src.asInstanceOf[StoredNode]
            val variable = varOf(e)
            enclosingStmt(src).foreach { srcStmt =>
              // intra-statement weave edges stay; edges arriving from another
              // statement's subtree must come from a definition carrier — and
              // when they do not, resolve back through the chain to the ones
              // that do, rather than dropping the dependence.
              if subtreeIds.contains(srcStmt.id()) || isDefCarrier(srcStmt) then
                emitDdgEdge(srcStmt, dstStmt, variable)
              else
                resolveCarriers(src, variable).foreach(emitDdgEdge(_, dstStmt, variable))
            }
          }
        }
      }

      // ── observable output ordering ─────────────────────────────────────────
      // Two println calls carry no data dependence between them, yet their
      // relative order *is* the program's output. Joern chains REACHING_DEF
      // through the System.out receiver across statements, and the def-carrier
      // rule above discards that as value availability — correct for slicing
      // precision, but it left *nothing* ordering observable output, so a merge
      // could emit two prints in an order matching neither contributor. Recover
      // it at statement level, which is what the dependence actually is: both
      // statements write to the same stream, so their order is behaviour.
      //
      // Emitted as its own kind, OUT, not as DDG: modelling it as a flow
      // dependence would chain every print to every other and collapse
      // precision. HPR answered the same problem the same way for def-order
      // (§4.1.2) — the edge exists but slices never traverse it. Only
      // `feasibility` reads it, as a precedence constraint on emission.
      m.cfgNode.foreach { n =>
        n.inE(EdgeTypes.REACHING_DEF).foreach { e =>
          val variable = varOf(e)
          if streamReceivers.contains(variable) then
            for
              srcStmt <- enclosingBlockStmt(e.src.asInstanceOf[StoredNode])
              dstStmt <- enclosingBlockStmt(n)
            do emitEdge(srcStmt, dstStmt, variable, "OUT")
        }
      }

      // DDG into the method return: keep only genuine return-value flow
      // (RETURN → METHOD_RETURN). Joern additionally emits a def-reaches-exit
      // REACHING_DEF for every definition; with a single METHOD_RETURN vertex
      // those collapse HPR's per-variable FinalUse structure into one
      // universal join point — any edit on either side rewires RET, so every
      // two-sided merge would falsely interfere. Phase two's param-out edges
      // reintroduce final state per variable, properly.
      ret.foreach { r =>
        r.inE(EdgeTypes.REACHING_DEF).foreach { e =>
          val src = e.src.asInstanceOf[StoredNode]
          val variable = varOf(e)
          enclosingStmt(src).filter(_.label == "RETURN").foreach { srcStmt =>
            emitDdgEdge(srcStmt, r, variable)
          }
        }
      }

      // ── def-order dependences (HPR §4.1) ────────────────────────────────────
      // HPR's third dependence kind. A PDG
      // contains v1 ->do(v3) v2 iff (1) v1 and v2 are both assignment
      // statements defining the same variable; (2) they lie in the same branch
      // of every conditional enclosing both; (3) some component v3 exists with
      // v1 ->f v3 and v2 ->f v3; (4) v1 is left of v2 in the AST. One edge per
      // witness v3, as HPR label them.
      //
      // Def-order rather than anti-/output dependence: HPR §4.1.1 omit those
      // "in favor of def-order dependences", since they render merged graphs
      // infeasible when they should merge and distinguish strongly equivalent
      // programs (§6.1). Slices never traverse a DO edge; it lands in the
      // in-edge signature AP compares.

      // clause (2), read off the AST because our CDG edges carry no branch
      // polarity: walk up from a vertex recording, for each enclosing
      // CONTROL_STRUCTURE, which of its children we came through. Two vertices
      // are in the same branch iff every shared conditional agrees.
      def branchPath(n: StoredNode): Map[Long, Long] =
        val out = mutable.Map.empty[Long, Long]
        var cur: StoredNode = n
        var steps = 0
        var done = false
        while !done && steps < 64 do
          val parent = astParentOf(cur)
          parent match
            case Some(p) =>
              if p.label == "CONTROL_STRUCTURE" then out(p.id()) = cur.id()
              cur = p
            case None => done = true
          steps += 1
        out.toMap

      def sameBranch(a: StoredNode, b: StoredNode): Boolean =
        val pa = branchPath(a)
        val pb = branchPath(b)
        pa.forall { case (cs, child) => pb.get(cs).forall(_ == child) }

      // clause (1)'s "assignment statement": a statement occupying a slot in a
      // block, or a parameter (HPR's initial-definition vertex). Excluding
      // nested sub-expression assignments also avoids pairing a statement with
      // a definition inside its own subtree.
      def isDefOrderCandidate(n: StoredNode): Boolean =
        definedVars(n).nonEmpty && n.label != "CONTROL_STRUCTURE" && (
          n.label == "METHOD_PARAMETER_IN" || isBlockChild(n))

      val doCandidates = (params ++ body).filter(isDefOrderCandidate).distinctBy(_.id())
      for
        v1 <- doCandidates
        v2 <- doCandidates
        if summon[Ordering[(Int, Int, Long)]].lt(posKey(v1), posKey(v2))   // (4)
        x  <- definedVars(v1).toSet.intersect(definedVars(v2).toSet)       // (1)
        if sameBranch(v1, v2)                                             // (2)
        w  <- ddgTargets.getOrElse((v1.id(), x), mutable.Set.empty)
                .intersect(ddgTargets.getOrElse((v2.id(), x), mutable.Set.empty))
        if idOf.contains(w)                                               // (3)
      do emitEdge(v1, v2, x, "DO", witness = Some(w))

      // ── CDG: entry edges (synthesized per HRB) + Joern's own CDG edges ─────
      val seenCdg = mutable.Set.empty[(Long, Long)]
      // `branch` labels a control dependence with the value the predicate must
      // take for the statement to run — HPR §4.1: "Control dependence edges are
      // labeled either true or false". Without it a guarded block and its
      // `else` are indistinguishable, so reconstitution emitted both inside the
      // `if` and the corpus could not contain a single if/else.
      // statements that a *control structure* already guards. HRB keep only the
      // immediate control dependence, and for these that is the guard we just
      // synthesized from the AST — so Joern's additional edge from an enclosing
      // predicate must not be added as a second parent. Scoped deliberately to
      // structure-guarded statements: a top-level statement after an early
      // `return` is guarded by the method entry, and there Joern's predicate
      // edge is the *nearer* one, so it is left alone (that case needs
      // post-dominance placement and stays out of scope).
      val structureGuarded = mutable.Map.empty[Long, Long]
      val guardOwner       = mutable.Map.empty[Long, StoredNode]   // condition -> its control structure
      val hasElse          = mutable.Set.empty[Long]               // control structures with an `else`

      def addCdg(src: StoredNode, dst: StoredNode, branch: Option[Boolean] = None): Unit =
        if idOf.contains(src.id()) && idOf.contains(dst.id()) then
          val key = (src.id(), dst.id())
          if !seenCdg.contains(key) then
            seenCdg += key
            val brField = branch.map(b => s", \"branch\": $b").getOrElse("")
            edgesJson += s"        { \"src\": ${jStr(idOf(src.id()))}, \"dst\": ${jStr(idOf(dst.id()))}, \"kind\": \"CDG\"${brField} }"

      // The same synthesis one level down. Joern's own CDG points a control
      // structure's condition at the *condition* of a nested control structure
      // and never at the nested CONTROL_STRUCTURE vertex itself, so a nested
      // `if` arrived with no incoming CDG edge at all: reconstitution had
      // nowhere to place it and the whole guarded block vanished from the
      // emitted program (found by the round-trip invariant, on `nested_control`
      // — a Type-I fixture whose emission the corpus never reached). HRB's rule
      // is that a predicate controls the statements of the block it guards;
      // apply it to every block, not only the method's.
      vertices.foreach { v =>
        if v.label == "CONTROL_STRUCTURE" then
          val kids = v match
            case a: AstNode => a.astChildren.l
            case _          => Nil
          // javasrc2cpg gives an `else` its own CONTROL_STRUCTURE vertex (code
          // "else") holding the alternative block, rather than a second block
          // under the `if`. So a control structure guards its body either by
          // its condition — `if`, `while` — or, having none, by itself.
          val cond   = kids.find(_.label != "BLOCK")
          val guard  = cond.getOrElse(v)
          val bodies = cond.map(c => kids.filter(_.id() != c.id())).getOrElse(kids)
          cond.foreach(c => guardOwner(c.id()) = v)
          if bodies.exists(b => b.label == "CONTROL_STRUCTURE") then hasElse += v.id()
          // Branch bodies in AST order: index 0 runs when the predicate holds,
          // index 1 when it does not. A `while` has only the first; an `if` has
          // the then-block and, where present, the `else` vertex.
          bodies.zipWithIndex.foreach { case (body, idx) =>
            val branch = cond.map(_ => idx == 0)
            val stmts =
              if body.label == "BLOCK" then body.astChildren.l
              else List(body)            // `if (c) stmt;` without braces
            stmts.foreach {
              case st: StoredNode if isStatementVertex(st) =>
                addCdg(guard, st, branch)
                structureGuarded(st.id()) = guard.id()
              case _ =>
            }
          }
      }

      // Early exit. `if (c) { return …; } tail;` leaves `tail` running exactly
      // when c is false, so its *immediate* control dependence is the predicate
      // — not the method entry, which is merely the outer one. Joern supplies
      // the edge (by post-dominance) but no polarity. Adding an entry edge as
      // well would give the statement two control parents, which Type II reads
      // as infeasible and reconstitution cannot place.
      //
      // Scoped to the shape that actually arises: a control structure with no
      // `else`, whose predicate Joern makes something outside the guarded block
      // control-dependent on. With both branches present a following statement
      // is reachable either way and is not control-dependent on the predicate
      // at all, unless one branch exits — which needs the CFG to tell, and is
      // left alone.
      vertices.foreach { v =>
        guardOwner.get(v.id()).foreach { cs =>
          if !hasElse.contains(cs.id()) then
            v.out(EdgeTypes.CDG).foreach {
              // real statements only: a sub-expression is never emitted, so it
              // needs no guard and labelling it only adds noise
              case dst: StoredNode
                if idOf.contains(dst.id())
                  && dst.id() != v.id()
                  && isBlockChild(dst)
                  && !structureGuarded.contains(dst.id()) =>
                addCdg(v, dst, Some(false))
                structureGuarded(dst.id()) = v.id()
              case _ =>
            }
        }
      }

      // HRB entry→child edges. Synthesized last, and only where nothing nearer
      // controls the statement: HRB keep the *immediate* control dependence.
      params.foreach(p => addCdg(m, p))
      ret.foreach(r => addCdg(m, r))
      m.block.astChildren.foreach {
        case c: StoredNode if isStatementVertex(c) && !structureGuarded.contains(c.id()) =>
          addCdg(m, c)
        case _ =>
      }

      // Joern's own CDG edges (branch / loop dependencies)
      vertices.foreach { v =>
        v.out(EdgeTypes.CDG).foreach {
          case dst: StoredNode if idOf.contains(dst.id()) =>
            if !structureGuarded.get(dst.id()).exists(_ != v.id()) then addCdg(v, dst)
          case _ =>
        }
      }

      val mJson =
        s"""    {
           |      "fullName": ${jStr(m.fullName)},
           |      "filename": ${jStr(m.filename)},
           |      "signature": ${jStr(m.signature)},
           |      "nodes": [
           |${nodesJson.mkString(",\n")}
           |      ],
           |      "edges": [
           |${edgesJson.mkString(",\n")}
           |      ]
           |    }""".stripMargin
      methodsJson += mJson
    }

    // ── interprocedural SDG edges: CALL / PARAM_IN / PARAM_OUT ──────────────
    // Statement-level mapping of HRB's call linkage: the call-site CALL vertex
    // doubles as the bundle of actual-in/actual-out vertices. CALL edge =
    // call site → callee entry; PARAM_IN = call site → each formal-in
    // (METHOD_PARAMETER_IN, variable = parameter name); PARAM_OUT = callee
    // METHOD_RETURN → call site (non-void callees only — the call expression
    // carries the returned value onward intra-procedurally). Bundling the
    // actuals over-approximates per-argument flow (every argument appears to
    // reach every parameter through the shared call vertex) — conservative
    // for interference detection; per-argument actual vertices are a
    // documented refinement.
    val byFullName = internalMethods.map(m => m.fullName -> m).toMap
    val interEdges = mutable.ArrayBuffer.empty[String]
    val seenInter  = mutable.Set.empty[(Long, Long, String)]

    def addInter(src: StoredNode, srcMfn: String, dst: StoredNode, dstMfn: String,
                 kind: String, variable: String): Unit =
      val key = (src.id(), dst.id(), kind + "/" + variable)
      if !seenInter.contains(key) then
        seenInter += key
        val varField = if variable.isEmpty then "" else s", \"variable\": ${jStr(variable)}"
        interEdges += s"    { \"src\": ${jStr(vid(src, srcMfn))}, \"dst\": ${jStr(vid(dst, dstMfn))}, \"kind\": ${jStr(kind)}$varField }"

    internalMethods.foreach { caller =>
      caller.cfgNode.foreach {
        case c: Call if byFullName.contains(c.methodFullName) =>
          val callee = byFullName(c.methodFullName)
          addInter(c, caller.fullName, callee, callee.fullName, "CALL", "")
          callee.parameter.l.foreach { p =>
            addInter(c, caller.fullName, p, callee.fullName, "PARAM_IN", p.property(Properties.Name))
          }
          val ret = callee.methodReturn
          if ret.property(Properties.TypeFullName) != "void" then
            addInter(ret, callee.fullName, c, caller.fullName, "PARAM_OUT", "<return>")
        case _ =>
      }
    }

    val doc =
      s"""{
         |  "version": ${jStr(version)},
         |  "methods": [
         |${methodsJson.mkString(",\n")}
         |  ],
         |  "interproceduralEdges": [
         |${interEdges.mkString(",\n")}
         |  ]
         |}
         |""".stripMargin

    Files.writeString(Paths.get(outPath), doc)

  // export one Base/A/B triple living in `dir`; output lands in dir-local
  // cpgs/ and pdg_json/ so every corpus fixture is self-contained
  def exportTriple(dir: String): Unit =
    val cpgDir  = s"$dir/cpgs"
    val jsonDir = s"$dir/pdg_json"
    Files.createDirectories(Paths.get(cpgDir))
    Files.createDirectories(Paths.get(jsonDir))
    println(s"[=] Triple: $dir")

    targets.foreach { case (filename, version) =>
      val inputPath = s"$dir/$filename"
      val binPath   = s"$cpgDir/$version.cpg.bin"
      val jsonPath  = s"$jsonDir/$version.json"

      println(s"[*] Creating CPG for $filename ...")
      val config = Config().withInputPath(inputPath).withOutputPath(binPath)

      new JavaSrc2Cpg().createCpg(config) match
        case Success(cpg) =>
          X2Cpg.applyDefaultOverlays(cpg)
          val ctx = new LayerCreatorContext(cpg)
          new OssDataFlow(new OssDataFlowOptions()).run(ctx)

          val nReaching = cpg.method.flatMap(_.cfgNode).flatMap(_.inE(EdgeTypes.REACHING_DEF)).size
          val nCdg      = cpg.method.flatMap(_.cfgNode).flatMap(_.inE(EdgeTypes.CDG)).size
          println(s"    [check] REACHING_DEF=$nReaching  CDG=$nCdg")

          exportCpg(cpg, version, jsonPath)
          println(s"    -> PDG JSON saved to $jsonPath")
          cpg.close()
        case Failure(err) =>
          System.err.println(s"    ERROR for $filename: ${err.getMessage}")
    }

  // export `root`, which is either a triple directory (it holds base.java) or a
  // directory of triple directories
  def exportRoot(root: String): Unit =
    val p = Paths.get(root)
    if Files.exists(p.resolve("base.java")) then exportTriple(root)
    else if Files.isDirectory(p) then
      Files.list(p).iterator().asScala.toList
        .filter(q => Files.isDirectory(q) && Files.exists(q.resolve("base.java")))
        .sortBy(_.getFileName.toString)
        .foreach(q => exportTriple(q.toString))
    else System.err.println(s"[!] no triples under $root")

  def main(args: Array[String]): Unit =
    // With no arguments: the root triple (the running dev example), then every
    // corpus fixture — the default every earlier milestone relied on. With
    // arguments: only those roots, which is how the step-27 invariant fuzzer
    // exports a scratch batch without touching examples/corpus.
    if args.nonEmpty then args.foreach(exportRoot)
    else
      exportTriple(baseDir)
      exportRoot(s"$baseDir/corpus")

    println("\n[+] Done.")