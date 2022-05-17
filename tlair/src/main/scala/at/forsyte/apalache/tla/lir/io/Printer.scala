package at.forsyte.apalache.tla.lir.io

import at.forsyte.apalache.tla.lir._
import at.forsyte.apalache.tla.lir.oper._
import at.forsyte.apalache.tla.lir.values._

/**
 * Note: consider inmplementing priority of operations. Jure, 24.11.2017
 */

abstract class Printer {
  def apply(p_ex: TlaEx): String

  def apply(p_decl: TlaDecl): String = {
    // Telling the compiler we know we're not using p_decl here
    locally(p_decl);
    ""
  }
}

object UTFPrinter extends Printer {

  val m_neq = "\u2260"
  val m_and = "\u2227"
  val m_or = "\u2228"
  val m_not = "\u00AC"
  val m_in = "\u2208"
  val m_notin = "\u2209"
  val m_impl = "\u21D2"
  val m_equiv = "\u21D4"
  val m_le = "\u2264"
  val m_ge = "\u2265"
  val m_forall = "\u2200"
  val m_exists = "\u2203"
  val m_cdot = "\u22C5"
  val m_box = "\u2610"
  val m_diamond = "\u2662"
  val m_rarrow = "\u2192"
  val m_ring = "\u2218"
  val m_guarantee = "\u2945"
  val m_leadsto = "\u21DD"
  val m_mapto = "\u21A6"
  val m_cap = "\u2229"
  val m_cup = "\u222A"
  val m_subset = "\u2282"
  val m_subseteq = "\u2286"
  val m_supset = "\u2283"
  val m_supseteq = "\u2287"
  val m_setminus = "\u2216"
  val m_times = "\u00D7"
  val m_defeq = "\u225C"

  def pad(s: String): String = " %s ".format(s)

  override def apply(p_ex: TlaEx): String = apply(p_ex, false)

  def apply(p_ex: TlaEx, p_rmSpace: Boolean): String = {
    def mapMk(seq: Seq[TlaEx], sep: String, fn: TlaEx => String) = seq.map(fn).mkString(sep)

    def str(seq: Seq[TlaEx], sep: String = ", ") = mapMk(seq, sep, apply)

    def opAppStr(seq: Seq[TlaEx], sep: String) = mapMk(seq, sep, opApp)

    def groupMapMk(
        seq: Seq[TlaEx],
        n: Int,
        pattern: String,
        sep: String,
        fn: TlaEx => String) =
      seq.grouped(n).toSeq.map(s => pattern.format(s.map(fn): _*)).mkString(sep)

    def opAppPattern(
        seq: Seq[TlaEx],
        n: Int,
        pattern: String,
        sep: String): String =
      groupMapMk(seq, n, pattern, sep, opApp)

    def opAppStrPairs(seq: Seq[TlaEx], mid: String = pad(m_rarrow), sep: String = pad(m_box)): String =
      opAppPattern(seq, 2, "%%s%s%%s".format(mid), sep)
    //      seq.grouped( 2 ).toSeq.map( s => s.map( apply ).mkString( mid ) ).mkString( sep )

    def opApp(p_ex: TlaEx): String = {
      p_ex match {
        case OperEx(TlaSetOper.enumSet | TlaSetOper.in | TlaFunOper.app, _*) => apply(p_ex)
        case OperEx(_, args @ _*) if args.size > 1                           => "(%s)".format(apply(p_ex))
        case _                                                               => apply(p_ex)
      }
    }

    def mkApp(formatString: String, args: TlaEx*) = formatString.format(args.map(apply): _*)

    def mkOpApp(formatString: String, args: TlaEx*) = formatString.format(args.map(opApp): _*)

    val ret = p_ex match {
      case NullEx       => "<[NULL]>"
      case NameEx(name) => name
      case ValEx(v) =>
        v match {
          case TlaInt(i)       => i.toString
          case TlaDecimal(d)   => d.toString
          case TlaStr(s)       => "\"" + s + "\""
          case TlaBool(b)      => if (b) "TRUE" else "FALSE"
          case s: TlaPredefSet => s.name
          case _               => ""
        }

      case LetInEx(body, defs @ _*) =>
        val defStrings = defs.map(apply(_)).mkString(" ")
        s"LET $defStrings IN ${apply(body)}"

      case OperEx(oper, args @ _*) =>
        oper match {
          case TlaOper.eq              => mkOpApp("%s = %s", args: _*)
          case TlaOper.ne              => mkOpApp("%%s %s %%s".format(m_neq), args: _*)
          case TlaOper.apply           => "%s(%s)".format(opApp(args.head), str(args.tail))
          case TlaOper.chooseUnbounded => mkOpApp("CHOOSE %s : %s", args: _*)
          case TlaOper.chooseBounded   => mkOpApp("CHOOSE %%s %s %%s : %%s".format(m_in), args: _*)

          case TlaBoolOper.and             => opAppStr(args, " %s ".format(m_and))
          case TlaBoolOper.or              => opAppStr(args, " %s ".format(m_or))
          case TlaBoolOper.not             => mkOpApp("%s%%s".format(m_not), args: _*)
          case TlaBoolOper.implies         => mkOpApp("%%s %s %%s".format(m_impl), args: _*)
          case TlaBoolOper.equiv           => mkOpApp("%%s %s %%s".format(m_equiv), args: _*)
          case TlaBoolOper.forall          => mkOpApp("%s%%s %s %%s: %%s".format(m_forall, m_in), args: _*)
          case TlaBoolOper.exists          => mkOpApp("%s%%s %s %%s: %%s".format(m_exists, m_in), args: _*)
          case TlaBoolOper.forallUnbounded => mkOpApp("%s%%s: %%s".format(m_forall), args: _*)
          case TlaBoolOper.existsUnbounded => mkOpApp("%s%%s: %%s".format(m_exists), args: _*)

          case TlaArithOper.plus    => mkOpApp("%s + %s", args: _*)
          case TlaArithOper.uminus  => mkOpApp("-%s", args: _*)
          case TlaArithOper.minus   => mkOpApp("%s - %s", args: _*)
          case TlaArithOper.mult    => mkOpApp("%s * %s", args: _*)
          case TlaArithOper.div     => mkOpApp("%s // %s", args: _*)
          case TlaArithOper.mod     => mkOpApp("%s %% %s", args: _*)
          case TlaArithOper.realDiv => mkOpApp("%s / %s", args: _*)
          case TlaArithOper.exp     => mkOpApp("%s ^ %s", args: _*)
          case TlaArithOper.dotdot  => mkOpApp("%s .. %s", args: _*)
          case TlaArithOper.lt      => mkOpApp("%s < %s", args: _*)
          case TlaArithOper.gt      => mkOpApp("%s > %s", args: _*)
          case TlaArithOper.le      => mkOpApp("%%s %s %%s".format(m_le), args: _*)
          case TlaArithOper.ge      => mkOpApp("%%s %s %%s".format(m_ge), args: _*)

          case TlaActionOper.prime       => mkOpApp("%s'", args: _*)
          case TlaActionOper.stutter     => mkOpApp("[%s]_%s", args: _*)
          case TlaActionOper.nostutter   => mkOpApp("<%s>_%s", args: _*)
          case TlaActionOper.enabled     => mkOpApp("ENABLED %s", args: _*)
          case TlaActionOper.unchanged   => mkOpApp("UNCHANGED %s", args: _*)
          case TlaActionOper.composition => mkOpApp("%%s %s %%s".format(m_cdot), args: _*)

          case TlaControlOper.caseNoOther => "CASE %s".format(opAppStrPairs(args))
          case TlaControlOper.caseWithOther =>
            "CASE %s %s OTHER %s %s".format(opAppStrPairs(args.tail), m_box, m_rarrow, args.head)
          case TlaControlOper.ifThenElse => mkOpApp("IF %s THEN %s ELSE %s", args: _*)

          case TlaTempOper.AA             => mkOpApp("[%s]%%s . %%s".format(m_forall), args: _*)
          case TlaTempOper.box            => mkOpApp("%s%%s".format(m_box), args: _*)
          case TlaTempOper.diamond        => mkOpApp("%s%%s".format(m_diamond), args: _*)
          case TlaTempOper.EE             => mkOpApp("[%s]%%s . %%s".format(m_exists), args: _*)
          case TlaTempOper.guarantees     => mkOpApp("%%s %s %%s".format(m_guarantee), args: _*)
          case TlaTempOper.leadsTo        => mkOpApp("%%s %s %%s".format(m_leadsto), args: _*)
          case TlaTempOper.strongFairness => mkApp("SF_%s(%s)", args: _*)
          case TlaTempOper.weakFairness   => mkApp("WF_%s(%s)", args: _*)

          case TlaFiniteSetOper.cardinality => mkApp("Cardinality(%s)", args: _*)
          case TlaFiniteSetOper.isFiniteSet => mkApp("IsFiniteSet(%s)", args: _*)

          case TlaFunOper.app    => "%s[%s]".format(opApp(args.head), apply(args.tail.head))
          case TlaFunOper.domain => mkOpApp("DOMAIN %s", args: _*)
          case TlaFunOper.enum   => "[%s]".format(opAppStrPairs(args, pad(m_mapto), ", "))
          case TlaFunOper.except =>
            "[%s EXCEPT %s]".format(apply(args.head), opAppPattern(args.tail, 2, "![%s] = %s", ", "))
          case TlaFunOper.funDef =>
            "[%s %s %s]".format(opAppStrPairs(args.tail, pad(m_in), ", "), m_mapto, apply(args.head))
          case TlaFunOper.tuple => "<<%s>>".format(str(args))

          case TlaSeqOper.append => "Append(%s)".format(str(args))
          case TlaSeqOper.concat => mkOpApp("%%s %s %%s".format(m_ring), args: _*)
          case TlaSeqOper.head   => mkApp("Head(%s)", args: _*)
          case TlaSeqOper.tail   => mkApp("Tail(%s)", args: _*)
          case TlaSeqOper.len    => mkApp("Len(%s)", args: _*)

          case TlaSetOper.enumSet  => "{%s}".format(str(args))
          case TlaSetOper.in       => mkOpApp("%%s %s %%s".format(m_in), args: _*)
          case TlaSetOper.notin    => mkOpApp("%%s %s %%s".format(m_notin), args: _*)
          case TlaSetOper.cap      => mkOpApp("%%s %s %%s".format(m_cap), args: _*)
          case TlaSetOper.cup      => mkOpApp("%%s %s %%s".format(m_cup), args: _*)
          case TlaSetOper.filter   => mkOpApp("{%%s %s %%s: %%s}".format(m_in), args: _*)
          case TlaSetOper.funSet   => mkOpApp("[%%s %s %%s]".format(m_rarrow), args: _*)
          case TlaSetOper.map      => "{%s : %s}".format(apply(args.head), opAppStrPairs(args.tail, pad(m_in), ", "))
          case TlaSetOper.powerset => mkOpApp("SUBSET %s", args: _*)
          case TlaSetOper.recSet   => "[" + opAppStrPairs(args, ": ", ", ") + "]"
          case TlaSetOper.seqSet   => mkApp("Seq(%s)", args: _*)
          case TlaSetOper.setminus => mkOpApp("%%s %s %%s".format(m_setminus), args: _*)
          case TlaSetOper.subseteq => mkOpApp("%%s %s %%s".format(m_subseteq), args: _*)
          case TlaSetOper.times    => opAppStr(args, pad(m_times))
          case TlaSetOper.union    => mkOpApp("UNION %s", args: _*)
          case TlaOper.label =>
            val body = this(args.head)
            val label = this(args.tail.head)
            val argsStr = args.tail.tail.map(apply).mkString(", ")
            if (args.lengthCompare(2) > 0) {
              s"$label($argsStr):: $body"
            } else {
              s"$label:: $body"
            }

          case _ =>
            if (args.isEmpty)
              oper.name
            else "%s(%s)".format(oper.name, str(args))
          // , args: _*) // the default format
        }

      case _ => ""
    }

    if (p_rmSpace)
      ret.replaceAll(" ", "")
    else ret
  }

  /**
   * Print a declaration
   *
   * @param p_decl
   *   a declaration
   * @return
   *   a string representation of TLA+ declaration
   */
  override def apply(p_decl: TlaDecl): String = {
    def pr_param(p: OperParam): String = {
      val arity = p.arity
      val params =
        if (arity == 0) "" else "(%s)".format(1.to(arity).map(_ => "_").mkString(", "))
      p.name + params
    }

    p_decl match {
      case TlaConstDecl(name) =>
        "CONSTANT " + name

      case TlaVarDecl(name) =>
        "VARIABLE " + name

      case TlaAssumeDecl(body) =>
        apply(body)

      case TlaOperDecl(name, formalParams, body) =>
        val ps =
          if (formalParams.isEmpty)
            ""
          else "(%s)".format(formalParams.map(pr_param).mkString(", "))

        name + ps + s" ${m_defeq} " + apply(body)

      case _ =>
        throw new RuntimeException("Unexpected declaration: " + p_decl) // it should not happen
    }
  }
}

object SimplePrinter extends Printer {

  def getSimple(p_str: String): String = {
    p_str match {
      case UTFPrinter.m_neq       => "/="
      case UTFPrinter.m_and       => "/\\"
      case UTFPrinter.m_or        => "\\/"
      case UTFPrinter.m_not       => "~"
      case UTFPrinter.m_in        => "\\in"
      case UTFPrinter.m_notin     => "\\notin"
      case UTFPrinter.m_impl      => "=>"
      case UTFPrinter.m_equiv     => "<=>"
      case UTFPrinter.m_le        => "<="
      case UTFPrinter.m_ge        => ">="
      case UTFPrinter.m_forall    => "\\A"
      case UTFPrinter.m_exists    => "\\E"
      case UTFPrinter.m_cdot      => "."
      case UTFPrinter.m_box       => "[]"
      case UTFPrinter.m_diamond   => "<>"
      case UTFPrinter.m_rarrow    => "->"
      case UTFPrinter.m_ring      => "o"
      case UTFPrinter.m_guarantee => "-+->"
      case UTFPrinter.m_leadsto   => "~>"
      case UTFPrinter.m_mapto     => "|->"
      case UTFPrinter.m_cap       => "\\cap"
      case UTFPrinter.m_cup       => "\\cup"
      case UTFPrinter.m_subset    => "\\subset"
      case UTFPrinter.m_subseteq  => "\\subseteq"
      case UTFPrinter.m_supset    => "\\supset"
      case UTFPrinter.m_supseteq  => "\\supseteq"
      case UTFPrinter.m_setminus  => "\\"
      case UTFPrinter.m_times     => "x"
      case _                      => p_str
    }
  }

  override def apply(p_ex: TlaEx): String = UTFPrinter.apply(p_ex).map(c => getSimple(c.toString)).mkString
}

object FullPrinter extends Printer {
  override def apply(p_ex: TlaEx): String = ""
}

object UsableAsIdentifierPrinter extends Printer {
  val leftBracket = "d"
  val rightBracket = "b"

  def printInfixOperator(implicit args: Seq[String], operatorName: String): String = {
    leftBracket + args.mkString(s"${rightBracket}_${operatorName}_${leftBracket}") + rightBracket
  }

  def printPostfixOperator(args: Seq[String], operatorName: String): String = {
    s"${leftBracket}_${args.mkString(",")}_${rightBracket}${operatorName}"
  }

  def printPrefixOperator(args: Seq[String], operatorName: String): String = {
    s"${operatorName}${leftBracket}_${args.mkString(",")}_${rightBracket}"
  }

  def printUnboundedQuantiOperator(variable: String, body: String, operatorName: String): String = {
    s"${operatorName}_${variable}_COLON_${leftBracket}_${body}_${rightBracket}"
  }

  def printQuantiOperator(
      variable: String,
      set: String,
      body: String,
      operatorName: String): String = {
    s"${operatorName}_${variable}_IN_${set}_COLON_${leftBracket}_${body}_${rightBracket}"
  }

  override def apply(p_ex: TlaEx): String = {
    p_ex match {
      case NameEx(name) => return name
      case NullEx       => return "null"
      case OperEx(oper, args: Seq[_]) =>
        val strArgs = args.map(arg => this(arg.asInstanceOf[TlaEx]))
        oper match {
          case TlaOper.eq              => printInfixOperator(strArgs, "EQ")
          case TlaOper.ne              => printInfixOperator(strArgs, "NEQ")
          case TlaOper.apply           => printPrefixOperator(strArgs.tail, strArgs.head)
          case TlaOper.chooseUnbounded => printUnboundedQuantiOperator(strArgs(0), strArgs(1), "CHOOSE")
          case TlaOper.chooseBounded   => printQuantiOperator(strArgs(0), strArgs(1), strArgs(2), "CHOOSE")

          case TlaBoolOper.and             => printInfixOperator(strArgs, "AND")
          case TlaBoolOper.or              => printInfixOperator(strArgs, "OR")
          case TlaBoolOper.not             => printPrefixOperator(strArgs, "NOT")
          case TlaBoolOper.implies         => printInfixOperator(strArgs, "IMPLIES")
          case TlaBoolOper.equiv           => printInfixOperator(strArgs, "EQUIV")
          case TlaBoolOper.forall          => printQuantiOperator(strArgs(0), strArgs(1), strArgs(2), "FORALL")
          case TlaBoolOper.exists          => printQuantiOperator(strArgs(0), strArgs(1), strArgs(2), "EXISTS")
          case TlaBoolOper.forallUnbounded => printUnboundedQuantiOperator(strArgs(0), strArgs(1), "FORALL")
          case TlaBoolOper.existsUnbounded => printUnboundedQuantiOperator(strArgs(0), strArgs(1), "EXISTS")

          case TlaArithOper.plus    => printInfixOperator(strArgs, "PLUS")
          case TlaArithOper.uminus  => printPrefixOperator(strArgs, "MINUS")
          case TlaArithOper.minus   => printInfixOperator(strArgs, "MINUS")
          case TlaArithOper.mult    => printInfixOperator(strArgs, "MULT")
          case TlaArithOper.div     => printInfixOperator(strArgs, "DIV")
          case TlaArithOper.mod     => printInfixOperator(strArgs, "MOD")
          case TlaArithOper.realDiv => printInfixOperator(strArgs, "DIV")
          case TlaArithOper.exp     => printInfixOperator(strArgs, "POW")
          case TlaArithOper.dotdot  => printInfixOperator(strArgs, "DOTDOT")
          case TlaArithOper.lt      => printInfixOperator(strArgs, "LESSTHAN")
          case TlaArithOper.gt      => printInfixOperator(strArgs, "GREATERTHAN")
          case TlaArithOper.le      => printInfixOperator(strArgs, "LESSEQ")
          case TlaArithOper.ge      => printInfixOperator(strArgs, "GREATEREQ")

          case TlaActionOper.prime       => printPostfixOperator(strArgs, "PRIME")
          case TlaActionOper.stutter     => printPrefixOperator(strArgs, "STUTTER")
          case TlaActionOper.nostutter   => printPrefixOperator(strArgs, "NOSTUTTER")
          case TlaActionOper.enabled     => printPrefixOperator(strArgs, "ENABLED")
          case TlaActionOper.unchanged   => printPrefixOperator(strArgs, "UNCHANGED")
          case TlaActionOper.composition => printInfixOperator(strArgs, "DOT")

          case TlaControlOper.caseNoOther   => printPrefixOperator(strArgs, "CASE")
          case TlaControlOper.caseWithOther => printPrefixOperator(strArgs, "CASEOTHER")
          case TlaControlOper.ifThenElse    => s"IF_${strArgs(0)}_THEN_${strArgs(1)}_ELSE_${strArgs(2)}"

          case TlaTempOper.AA             => printUnboundedQuantiOperator(strArgs(0), strArgs(1), "TEMPORALFORALL")
          case TlaTempOper.box            => printPrefixOperator(strArgs, "BOX")
          case TlaTempOper.diamond        => printPrefixOperator(strArgs, "DIAMOND")
          case TlaTempOper.EE             => printUnboundedQuantiOperator(strArgs(0), strArgs(1), "TEMPORALEXISTS")
          case TlaTempOper.guarantees     => printInfixOperator(strArgs, "GUARANTEES")
          case TlaTempOper.leadsTo        => printInfixOperator(strArgs, "LEADSTO")
          case TlaTempOper.strongFairness => printPrefixOperator(strArgs, "STRONGFAIR")
          case TlaTempOper.weakFairness   => printPrefixOperator(strArgs, "WEAKFAIR")

          case TlaFiniteSetOper.cardinality => printPrefixOperator(strArgs, "CARDINALITY")
          case TlaFiniteSetOper.isFiniteSet => printPrefixOperator(strArgs, "ISFINITESET")

          case TlaFunOper.app    => printPrefixOperator(strArgs.tail, strArgs.head)
          case TlaFunOper.domain => printPrefixOperator(strArgs, "DOMAIN")
          case TlaFunOper.enum   => printPrefixOperator(strArgs, "ENUM")
          case TlaFunOper.except => printPrefixOperator(strArgs, "EXCEPT")
          case TlaFunOper.funDef => printPrefixOperator(strArgs, "FUNDEF")
          case TlaFunOper.tuple  => s"TUPLE${leftBracket}_${strArgs.mkString(",")}_${rightBracket}"

          case TlaSeqOper.append => printPrefixOperator(strArgs, "APPEND")
          case TlaSeqOper.concat => printInfixOperator(strArgs, "CONCAT")
          case TlaSeqOper.head   => printPrefixOperator(strArgs, "HEAD")
          case TlaSeqOper.tail   => printPrefixOperator(strArgs, "TAIL")
          case TlaSeqOper.len    => printPrefixOperator(strArgs, "LEN")

          case TlaSetOper.enumSet => printPrefixOperator(strArgs, "SET")
          case TlaSetOper.in      => printInfixOperator(strArgs, "IN")
          case TlaSetOper.notin   => printInfixOperator(strArgs, "NOTIN")
          case TlaSetOper.cap     => printInfixOperator(strArgs, "CAP")
          case TlaSetOper.cup     => printInfixOperator(strArgs, "CUP")
          case TlaSetOper.filter =>
            s"SET_${leftBracket}${printQuantiOperator(strArgs(0), strArgs(1), strArgs(2), "")}${rightBracket}"
          case TlaSetOper.funSet   => s"FUNCTIONSET_" + printInfixOperator(strArgs, "RIGHTARROW")
          case TlaSetOper.map      => s"MAP" + printInfixOperator(strArgs, "COLON")
          case TlaSetOper.powerset => printPrefixOperator(strArgs, "POWERSET")
          case TlaSetOper.recSet   => printPrefixOperator(strArgs, "RECSET")
          case TlaSetOper.seqSet   => printPrefixOperator(strArgs, "SEQ")
          case TlaSetOper.setminus => printInfixOperator(strArgs, "SETMINUS")
          case TlaSetOper.subseteq => printInfixOperator(strArgs, "SUBSETEQ")
          case TlaSetOper.times    => printInfixOperator(strArgs, "TIMES")
          case TlaSetOper.union    => printInfixOperator(strArgs, "UNION")
          case TlaOper.label       => throw new NotImplementedError("Printing labels as identifiers is not supported")

          case _ =>
            if (args.isEmpty)
              oper.name
            else printPrefixOperator(strArgs, oper.name)
          // , args: _*) // the default format
        }

      case ValEx(value) =>
        value match {
          case TlaInt(i)       => (if (i < 0) "MINUS" else "") + i.abs.toString
          case TlaDecimal(d)   => (if (d < 0) "MINUS" else "") + d.abs.toString
          case TlaStr(s)       => s.replaceAll("/[^A-Za-z0-9_]/", "_")
          case TlaBool(b)      => if (b) "TRUE" else "FALSE"
          case s: TlaPredefSet => s.name.replaceAll("/[^A-Za-z0-9_]/", "_")
          case _               => ""
        }
      case LetInEx(_, _) =>
        throw new NotImplementedError("Printing Let-In expressions as identifiers is not supported")
      case _ =>
        throw new NotImplementedError(
            s"Printing expression as identifier is not supported for expression ${p_ex.toString()}"
        )
    }
  }
}
