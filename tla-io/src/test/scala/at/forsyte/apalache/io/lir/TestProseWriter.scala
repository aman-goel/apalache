package at.forsyte.apalache.io.lir

import at.forsyte.apalache.tla.lir.TypedPredefs.BuilderExAsTyped
import at.forsyte.apalache.tla.lir.UntypedPredefs._
import at.forsyte.apalache.tla.lir._
import at.forsyte.apalache.tla.lir.aux.SmileyFunFun._
import at.forsyte.apalache.tla.lir.convenience.tla
import at.forsyte.apalache.tla.lir.convenience.tla._
import at.forsyte.apalache.tla.lir.oper.{TlaArithOper, TlaFunOper, TlaOper}
import at.forsyte.apalache.tla.lir.values.TlaInt
import org.junit.runner.RunWith
import org.scalatest.junit.JUnitRunner
import org.scalatest.{BeforeAndAfterEach, FunSuite}

import java.io.{PrintWriter, StringWriter}

@RunWith(classOf[JUnitRunner])
class TestProseWriter extends FunSuite with BeforeAndAfterEach {
  private var stringWriter = new StringWriter()
  private var printWriter = new PrintWriter(stringWriter)
  private val layout80 = TextLayout().copy(textWidth = 80)
  private val layout40 = TextLayout().copy(textWidth = 40)
  private val layout30 = TextLayout().copy(textWidth = 30)
  private val layout20 = TextLayout().copy(textWidth = 20)
  private val layout15 = TextLayout().copy(textWidth = 15)
  private val layout10 = TextLayout().copy(textWidth = 10)

  override protected def beforeEach(): Unit = {
    stringWriter = new StringWriter()
    printWriter = new PrintWriter(stringWriter)
  }

  test("name") {
    val writer = new ProseWriter(printWriter, layout80)
    writer.write(name("awesome"))
    printWriter.flush()
    assert("awesome" == stringWriter.toString)
  }

  test("apply A") {
    val writer = new ProseWriter(printWriter, layout80)
    writer.write(OperEx(TlaOper.apply, name("A")))
    printWriter.flush()
    assert("A" == stringWriter.toString)
  }

  test("apply A!B") {
    val writer = new ProseWriter(printWriter, layout80)
    writer.write(OperEx(TlaOper.apply, name("A!B")))
    printWriter.flush()
    assert("A_i_B" == stringWriter.toString)
  }

  test("apply A$B") {
    val writer = new ProseWriter(printWriter, layout80)
    writer.write(OperEx(TlaOper.apply, name("A$B")))
    printWriter.flush()
    assert("A_si_B" == stringWriter.toString)
  }

  test("apply A to 1") {
    val writer = new ProseWriter(printWriter, layout80)
    writer.write(OperEx(TlaOper.apply, name("A"), int(1)))
    printWriter.flush()
    assert("A(1)" == stringWriter.toString)
  }

  test("apply A to 1 and 2") {
    val writer = new ProseWriter(printWriter, layout80)
    writer.write(OperEx(TlaOper.apply, name("A"), int(1), int(2)))
    printWriter.flush()
    assert("A(1, 2)" == stringWriter.toString)
  }

  test("assignment: x' := 2") {
    val writer = new ProseWriter(printWriter, layout80)
    writer.write(assignPrime(name("x"), int(2)))
    printWriter.flush()
    assert("x' := 2" == stringWriter.toString)
  }

  test("ENABLED and prime") {
    val writer = new ProseWriter(printWriter, layout80)
    writer.write(enabled(prime(name("x"))))
    printWriter.flush()
    assert("ENABLED x'" == stringWriter.toString)
  }

  test("UNCHANGED") {
    val writer = new ProseWriter(printWriter, layout80)
    writer.write(unchanged(name("x")))
    printWriter.flush()
    assert("UNCHANGED x" == stringWriter.toString)
  }

  test("[A]_vars") {
    val writer = new ProseWriter(printWriter, layout80)
    writer.write(stutt(name("A"), name("vars")))
    printWriter.flush()
    assert("[A]_vars" == stringWriter.toString)
  }

  test("<A>_vars") {
    val writer = new ProseWriter(printWriter, layout80)
    writer.write(nostutt(name("A"), name("vars")))
    printWriter.flush()
    assert("<A>_vars" == stringWriter.toString)
  }

  test("A \\cdot B") {
    val writer = new ProseWriter(printWriter, layout80)
    writer.write(comp(name("A"), name("B")))
    printWriter.flush()
    assert("A then B" == stringWriter.toString)
  }

  test("WF_vars(A)") {
    val writer = new ProseWriter(printWriter, layout80)
    writer.write(WF(name("vars"), name("A")))
    printWriter.flush()
    assert("WF_vars(A)" == stringWriter.toString)
  }

  test("SF_vars(A)") {
    val writer = new ProseWriter(printWriter, layout80)
    writer.write(SF(name("vars"), name("A")))
    printWriter.flush()
    assert("SF_vars(A)" == stringWriter.toString)
  }

  test("[]A") {
    val writer = new ProseWriter(printWriter, layout80)
    writer.write(box(name("A")))
    printWriter.flush()
    assert("[]A" == stringWriter.toString)
  }

  test("<>A") {
    val writer = new ProseWriter(printWriter, layout80)
    writer.write(diamond(name("A")))
    printWriter.flush()
    assert("<>A" == stringWriter.toString)
  }

  test("A ~> B") {
    val writer = new ProseWriter(printWriter, layout80)
    writer.write(leadsTo(name("A"), name("B")))
    printWriter.flush()
    assert("A ~> B" == stringWriter.toString)
  }

  test("A -+-> B") {
    val writer = new ProseWriter(printWriter, layout80)
    writer.write(guarantees(name("A"), name("B")))
    printWriter.flush()
    assert("A -+-> B" == stringWriter.toString)
  }

  test("empty set") {
    val writer = new ProseWriter(printWriter, layout80)
    writer.write(enumSet())
    printWriter.flush()
    assert("Empty set" == stringWriter.toString)
  }

  test("singleton set") {
    val writer = new ProseWriter(printWriter, layout80)
    writer.write(enumSet(int(42)))
    printWriter.flush()
    assert("{Set of 42}" == stringWriter.toString)
  }

  test("one-line set") {
    val writer = new ProseWriter(printWriter, layout80)
    writer.write(enumSet(int(1), int(2), int(3)))
    printWriter.flush()
    assert("{Set of 1, 2, 3}" == stringWriter.toString)
  }

  test("multi-line set") {
    val writer = new ProseWriter(printWriter, layout20)
    writer.write(enumSet(1.to(10).map(int): _*))
    printWriter.flush()
    val expected =
      """{Set of 1,
        |  2,
        |  3,
        |  4,
        |  5,
        |  6,
        |  7,
        |  8,
        |  9,
        |  10}""".stripMargin
    // Igor: I would prefer the layout below, but do not know how to do it with kiama
    val iLikeItBetterButItDoesNotWork =
      """{
        |  1,
        |  2,
        |  3,
        |  4,
        |  5,
        |  6,
        |  7,
        |  8,
        |  9,
        |  10
        |}""".stripMargin
    val result = stringWriter.toString
    assert(expected == result)
  }

  test("singleton tuple") {
    val writer = new ProseWriter(printWriter, layout80)
    writer.write(tuple(int(1)))
    printWriter.flush()
    assert("(1,)" == stringWriter.toString)
  }

  test("one-line tuple") {
    val writer = new ProseWriter(printWriter, layout80)
    writer.write(tuple(int(1), int(2), int(3)))
    printWriter.flush()
    assert("(1, 2, 3)" == stringWriter.toString)
  }

  test("multi-line tuple") {
    val writer = new ProseWriter(printWriter, layout20)
    writer.write(tuple(1.to(10).map(int): _*))
    printWriter.flush()
    val expected =
      """(
        |  1, 2, 3, 4, 5, 6, 7,
        |  8, 9, 10
        |)""".stripMargin
    assert(expected == stringWriter.toString)
  }

  test("one-line Cartesian product") {
    val writer = new ProseWriter(printWriter, layout80)
    writer.write(times(name("X"), name("Y"), name("Z")))
    printWriter.flush()
    assert("{Cross product of X, Y, Z}" == stringWriter.toString)
  }

  test("multi-line Cartesian product") {
    val writer = new ProseWriter(printWriter, layout40)
    writer.write(times(name("verylongname1"), name("verylongname2"), name("verylongname3")))
    printWriter.flush()
    val expected =
      """{Cross product of 
        |  verylongname1, verylongname2, verylongname3}""".stripMargin
    assert(expected == stringWriter.toString)
  }

  test("one-line conjunction") {
    val writer = new ProseWriter(printWriter, layout80)
    val expr = and(1.to(3) map (_ => name("verylongname")): _*)
    writer.write(expr)
    printWriter.flush()
    val expected =
      """verylongname and verylongname and verylongname""".stripMargin
    assert(expected == stringWriter.toString)
  }

  test("multi-line conjunction") {
    val writer = new ProseWriter(printWriter, layout40)
    val expr = impl(bool(true), and(1.to(5) map (_ => name("verylongname")): _*))
    writer.write(expr)
    printWriter.flush()
    // a multi-line vertical box always breaks from the previous line, as otherwise it is incredibly hard to indent
    val expected =
      """TRUE
        |  implies verylongname
        |    and verylongname
        |    and verylongname
        |    and verylongname
        |    and verylongname""".stripMargin
    assert(expected == stringWriter.toString)
  }

  test("nested multiline conjunction/disjunction") {
    val writer = new ProseWriter(printWriter, layout80)
    val orEx = or(1.to(3) map (_ => name("verylongname")): _*)
    val andEx = and(1.to(3) map (_ => orEx): _*)
    writer.write(andEx)
    printWriter.flush()
    val expected =
      """(verylongname or verylongname or verylongname)
        |  and (verylongname or verylongname or verylongname)
        |  and (verylongname or verylongname or verylongname)""".stripMargin
    assert(expected == stringWriter.toString)
  }

  test("nested multiline conjunction under negation") {
    val writer = new ProseWriter(printWriter, layout20)
    val andEx = and(1.to(3) map (_ => name("verylongname")): _*)
    writer.write(not(andEx))
    printWriter.flush()
    val expected =
      """not(verylongname
        |  and verylongname
        |  and verylongname)""".stripMargin
    assert(expected == stringWriter.toString)
  }

  test("~x") {
    val writer = new ProseWriter(printWriter, layout80)
    writer.write(not(name("x")))
    printWriter.flush()
    assert("not(x)" == stringWriter.toString)
  }

  test("~(1 = 2)") {
    val writer = new ProseWriter(printWriter, layout80)
    writer.write(not(eql(int(1), int(2))))
    printWriter.flush()
    assert("not(1 = 2)" == stringWriter.toString)
  }

  test("[S -> T]") {
    val writer = new ProseWriter(printWriter, layout80)
    writer.write(funSet(name("S"), name("T")))
    printWriter.flush()
    val expected =
      """Set of functions
        |  from S
        |  to T""".stripMargin
    assert(expected == stringWriter.toString)
  }

  test("L2 :: 1") {
    val writer = new ProseWriter(printWriter, layout80)
    writer.write(label(int(1), "L2"))
    printWriter.flush()
    assert("L2 :: 1" == stringWriter.toString)
  }

  test("L2(a, b) :: 1") {
    val writer = new ProseWriter(printWriter, layout80)
    writer.write(label(int(1), "L2", "a", "b"))
    printWriter.flush()
    assert("L2(a, b) :: 1" == stringWriter.toString)
  }

  test("one-line exists") {
    val writer = new ProseWriter(printWriter, layout40)
    val expr = exists(name("x"), name("y"), name("z"))
    writer.write(expr)
    printWriter.flush()
    // a multi-line vertical box always breaks from the previous line, as otherwise it is incredibly hard to indent
    val expected = "Exists x in y such that z holds"
    assert(expected == stringWriter.toString)
  }

  test("multi-line exists") {
    val writer = new ProseWriter(printWriter, layout40)
    val expr =
      exists(name("verylongname1"), name("verylongname2"), name("verylongname3"))
    writer.write(expr)
    printWriter.flush()
    // a multi-line vertical box always breaks from the previous line, as otherwise it is incredibly hard to indent
    val expected =
      """Exists verylongname1 in verylongname2 such that
        |  verylongname3
        |  holds""".stripMargin
    assert(expected == stringWriter.toString)
  }

  test("nested quantifiers") {
    val writer = new ProseWriter(printWriter, layout40)
    val ex1 =
      exists(name("verylongname1"), name("verylongname2"), name("verylongname3"))
    val ex2 =
      forall(name("verylong4"), name("verylong5"), ex1)
    writer.write(ex2)
    printWriter.flush()
    // a multi-line vertical box always breaks from the previous line, as otherwise it is incredibly hard to indent
    val expected =
      """For each verylong4 in verylong5 holds
        |  Exists verylongname1 in verylongname2 such that
        |    verylongname3
        |    holds""".stripMargin
    assert(expected == stringWriter.toString)
  }

  test("nested \\EE and \\AA") {
    val writer = new ProseWriter(printWriter, layout10)
    val ex1 =
      EE(name("verylongname1"), name("verylongname2"))
    val ex2 =
      AA(name("verylong3"), ex1)
    writer.write(ex2)
    printWriter.flush()
    // a multi-line vertical box always breaks from the previous line, as otherwise it is incredibly hard to indent
    val expected =
      """\AA verylong3:
        |  \EE verylongname1:
        |    verylongname2""".stripMargin
    assert(expected == stringWriter.toString)
  }

  test("a one-line record") {
    val writer = new ProseWriter(printWriter, layout40)
    val expr = enumFun(
        str("x1"),
        name("x2"),
        str("x3"),
        name("x4"),
        str("x5"),
        name("x6"),
    ) ////
    writer.write(expr)
    printWriter.flush()
    val expected =
      """{x1: x2, x3: x4, x5: x6}""".stripMargin
    assert(expected == stringWriter.toString)
  }

  test("a multi-line record") {
    val writer = new ProseWriter(printWriter, layout40)
    val expr = enumFun(
        str("verylong1"),
        name("verylong2"),
        str("verylong3"),
        name("verylong4"),
        str("verylong5"),
        name("verylong6"),
    ) ////
    writer.write(expr)
    printWriter.flush()
    val expected =
      """{verylong1: verylong2,
        |  verylong3: verylong4,
        |  verylong5: verylong6}""".stripMargin
    assert(expected == stringWriter.toString)
  }

  test("a narrow multi-line record") {
    val writer = new ProseWriter(printWriter, layout20)
    val expr = enumFun(
        str("verylong1"),
        name("verylong2"),
        str("verylong3"),
        name("verylong4"),
        str("verylong5"),
        name("verylong6"),
    ) ////
    writer.write(expr)
    printWriter.flush()
    val expected =
      """{verylong1:
        |    verylong2,
        |  verylong3:
        |    verylong4,
        |  verylong5:
        |    verylong6}""".stripMargin
    assert(expected == stringWriter.toString)
  }

  test("TLC @@") {
    val writer = new ProseWriter(printWriter, layout40)

    val strToInt = FunT1(IntT1(), StrT1())
    val expr = funfun(strToInt, smiley(strToInt, str("a").typed(), int(1).typed()),
        funfun(strToInt, smiley(strToInt, str("b"), int(2)), smiley(strToInt, str("c"), int(3))))
    writer.write(expr)
    printWriter.flush()
    val expected = """"a" :> 1 @@ "b" :> 2 @@ "c" :> 3""".stripMargin
    assert(expected == stringWriter.toString)
  }

  test("a one-line set of records") {
    val writer = new ProseWriter(printWriter, layout40)
    val expr = recSet(
        str("x1"),
        name("x2"),
        str("x3"),
        name("x4"),
        str("x5"),
        name("x6"),
    ) ////
    writer.write(expr)
    printWriter.flush()
    val expected =
      """Set of records [x1 in x2,
        |  x3 in x4,
        |  x5 in x6]""".stripMargin
    assert(expected == stringWriter.toString)
  }

  test("a multi-line set of records") {
    val writer = new ProseWriter(printWriter, layout40)
    val expr = recSet(
        str("verylong1"),
        name("verylong2"),
        str("verylong3"),
        name("verylong4"),
        str("verylong5"),
        name("verylong6"),
    ) ////
    writer.write(expr)
    printWriter.flush()
    val expected =
      """Set of records [verylong1 in verylong2,
        |  verylong3 in verylong4,
        |  verylong5 in verylong6]""".stripMargin
    assert(expected == stringWriter.toString)
  }

  test("a one-line function") {
    val writer = new ProseWriter(printWriter, layout80)
    val expr = funDef(plus(name("x"), name("y")), name("x"), name("S"), name("y"), name("T"))
    writer.write(expr)
    printWriter.flush()
    val expected =
      """Function of [x in S, y in T] to x + y""".stripMargin
    assert(expected == stringWriter.toString)
  }

  test("a multi-line function") {
    val writer = new ProseWriter(printWriter, layout30)
    val expr = funDef(plus(name("verylong1"), name("verylong2")), name("verylong1"), name("verylong3"),
        name("verylong2"), name("verylong4"))
    writer.write(expr)
    printWriter.flush()
    val expected =
      """Function of
        |  [verylong1 in verylong3,
        |  verylong2 in verylong4] to
        |    verylong1 + verylong2""".stripMargin
    assert(expected == stringWriter.toString)
  }

  test("a one-line map") {
    val writer = new ProseWriter(printWriter, layout80)
    val expr = map(plus(name("x"), name("y")), name("x"), name("S"), name("y"), name("T"))
    writer.write(expr)
    printWriter.flush()
    val expected =
      """{Set of x + y} where {x in S, y in T}""".stripMargin
    assert(expected == stringWriter.toString)
  }

  test("a multi-line map") {
    val writer = new ProseWriter(printWriter, layout30)
    val expr = map(plus(name("verylong1"), name("verylong2")), name("verylong1"), name("verylong3"), name("verylong2"),
        name("verylong4"))
    writer.write(expr)
    printWriter.flush()
    val expected =
      """{Set of
        |  verylong1 + verylong2} where
        |  {verylong1 in verylong3,
        |  verylong2 in verylong4}""".stripMargin
    assert(expected == stringWriter.toString)
  }

  test("a one-line filter") {
    val writer = new ProseWriter(printWriter, layout80)
    val expr = filter(name("x"), name("S"), name("P"))
    writer.write(expr)
    printWriter.flush()
    val expected =
      """{Set of x in S} such that P holds""".stripMargin
    assert(expected == stringWriter.toString)
  }

  test("precedence in filter") {
    val writer = new ProseWriter(printWriter, layout80)
    val expr = filter(name("x"), name("S"), lt(name("x"), int(5)))
    writer.write(expr)
    printWriter.flush()
    val expected =
      """{Set of x in S} such that x < 5 holds""".stripMargin
    assert(expected == stringWriter.toString)
  }

  test("a multi-line filter") {
    val writer = new ProseWriter(printWriter, layout40)
    val expr = filter(name("verylongname1"), name("verylongname2"), name("verylongname3"))

    writer.write(expr)
    printWriter.flush()
    val expected =
      """{Set of verylongname1 in verylongname2}
        |  such that
        |  verylongname3
        |  holds""".stripMargin
    assert(expected == stringWriter.toString)
  }

  test("a one-line function application") {
    val writer = new ProseWriter(printWriter, layout80)
    val expr = appFun(name("f"), name("e"))
    writer.write(expr)
    printWriter.flush()
    val expected = """f[e]""".stripMargin
    assert(expected == stringWriter.toString)
  }

  test("a multi-line function application") {
    val writer = new ProseWriter(printWriter, layout20)
    val expr = appFun(name("verylongname1"), name("verylongname2"))
    writer.write(expr)
    printWriter.flush()
    val expected =
      """verylongname1[
        |  verylongname2
        |]""".stripMargin
    assert(expected == stringWriter.toString)
  }

  test("a one-line IF-THEN-ELSE") {
    val writer = new ProseWriter(printWriter, layout80)
    val expr = ite(name("a"), name("b"), name("c"))
    writer.write(expr)
    printWriter.flush()
    val expected = """if a then b else c""".stripMargin
    assert(expected == stringWriter.toString)
  }

  test("a multi-line IF-THEN-ELSE") {
    val writer = new ProseWriter(printWriter, layout20)
    val expr = ite(name("verylongname1"), name("verylongname2"), name("verylongname3"))
    writer.write(expr)
    printWriter.flush()
    val expected =
      """if verylongname1
        |then verylongname2
        |else verylongname3""".stripMargin
    assert(expected == stringWriter.toString)
  }

  test("a one-line EXCEPT") {
    val writer = new ProseWriter(printWriter, layout80)
    // recall that EXCEPT indices are always wrapped in a tuple
    val expr = except(name("f"), tuple(name("k")), name("v"))
    writer.write(expr)
    printWriter.flush()
    val expected = """[Copy function f except at k set v]""".stripMargin
    assert(expected == stringWriter.toString)
  }

  test("a two-argument EXCEPT") {
    val writer = new ProseWriter(printWriter, layout80)
    // recall that EXCEPT indices are always wrapped in a tuple
    val expr = except(name("f"), tuple(name("i"), name("k")), name("v"))
    writer.write(expr)
    printWriter.flush()
    val expected = """[Copy function f except at i, k set v]""".stripMargin
    assert(expected == stringWriter.toString)
  }

  test("a multi-line EXCEPT") {
    val writer = new ProseWriter(printWriter, layout40)
    val expr = except(
        name("verylongname1"),
        tuple(name("verylongname2")),
        name("verylongname3"),
    ) ///

    writer.write(expr)
    printWriter.flush()
    val expected =
      """[Copy function
        |  verylongname1 except
        |    at verylongname2 set verylongname3]""".stripMargin
    assert(expected == stringWriter.toString)
  }

  test("a monster EXCEPT") {
    val writer = new ProseWriter(printWriter, layout40)
    val expr = except(
        name("verylongname1"),
        tuple(name("verylongname2")),
        name("verylongname3"),
        tuple(name("verylongname4")),
        name("verylongname5"),
    ) ///

    writer.write(expr)
    printWriter.flush()
    val expected =
      """[Copy function
        |  verylongname1 except
        |    at verylongname2 set verylongname3,
        |    at verylongname4 set verylongname5]""".stripMargin
    assert(expected == stringWriter.toString)
  }

  test("FiniteSets!Cardinality") {
    val writer = new ProseWriter(printWriter, layout80)
    val expr = card(name("S"))
    writer.write(expr)
    printWriter.flush()
    val expected = """Cardinality(S)""".stripMargin
    assert(expected == stringWriter.toString)
  }

  test("<<a>> \\o <<b>>") {
    val writer = new ProseWriter(printWriter, layout80)
    val expr = concat(tuple(name("a")), tuple(name("b")))
    writer.write(expr)
    printWriter.flush()
    val expected = """Concat (a,) with (b,).""".stripMargin
    assert(expected == stringWriter.toString)
  }

  test("Sequences!Append(<<a>>, b)") {
    val writer = new ProseWriter(printWriter, layout80)
    val expr = append(tuple(name("a")), name("b"))
    writer.write(expr)
    printWriter.flush()
    val expected = """Append (a,) to b.""".stripMargin
    assert(expected == stringWriter.toString)
  }

  test("a multi-line CASE") {
    val writer = new ProseWriter(printWriter, layout40)
    val expr = caseSplit(name("guard1"), name("action1"), name("guard2"), name("action2"))
    writer.write(expr)
    printWriter.flush()
    val expected =
      """CASE guard1 -> action1
        |  [] guard2 -> action2""".stripMargin
    assert(expected == stringWriter.toString)
  }

  test("a concise multi-line CASE") {
    val writer = new ProseWriter(printWriter, layout15)
    val expr = caseSplit(name("guard1"), name("action1"), name("guard2"), name("action2"))
    writer.write(expr)
    printWriter.flush()
    val expected =
      """CASE guard1
        |    -> action1
        |  [] guard2
        |    -> action2""".stripMargin
    assert(expected == stringWriter.toString)
  }

  test("a multi-line CASE with OTHER") {
    val writer = new ProseWriter(printWriter, layout40)
    val expr = caseOther(name("otherAction"), name("guard1"), name("action1"), name("guard2"), name("action2"))
    writer.write(expr)
    printWriter.flush()
    val expected =
      """CASE guard1 -> action1
        |  [] guard2 -> action2
        |  [] OTHER -> otherAction""".stripMargin
    assert(expected == stringWriter.toString)
  }

  test("a one-line LET-IN") {
    val writer = new ProseWriter(printWriter, layout40)
    val aDecl = TlaOperDecl("A", List(), int(1))
    val expr = letIn(appDecl(aDecl), aDecl)
    writer.write(expr)
    printWriter.flush()
    val expected =
      """Let A be 1 in A""".stripMargin
    assert(expected == stringWriter.toString)
  }

  test("a multi-line LET-IN") {
    val writer = new ProseWriter(printWriter, layout40)
    val decl =
      TlaOperDecl("AVeryLongName", List(OperParam("param1"), OperParam("param2")), plus(name("param1"), name("param2")))
    val expr = letIn(appDecl(decl, int(1), int(2)), decl)
    writer.write(expr)
    printWriter.flush()
    val expected =
      """Let AVeryLongName(param1, param2) be
        |  param1 + param2
        |in
        |AVeryLongName(1, 2)""".stripMargin
    assert(expected == stringWriter.toString)
  }

  test("multiple definitions in LET-IN") {
    val writer = new ProseWriter(printWriter, layout40)
    val decl1 =
      TlaOperDecl("AVeryLongName", List(OperParam("param1"), OperParam("param2")), plus(name("param1"), name("param2")))
    val decl2 =
      TlaOperDecl("BVeryLongName", List(OperParam("param1"), OperParam("param2")), plus(name("param1"), name("param2")))
    val expr = letIn(mult(appDecl(decl1, int(1), int(2)), appDecl(decl2, int(3), int(4))), decl1, decl2)
    writer.write(expr)
    printWriter.flush()
    val expected =
      """Let AVeryLongName(param1, param2) be
        |  param1 + param2
        |in
        |Let BVeryLongName(param1, param2) be
        |  param1 + param2
        |in
        |AVeryLongName(1, 2)
        |  * BVeryLongName(3, 4)""".stripMargin
    assert(expected == stringWriter.toString)
  }

  test("a LAMBDA as LET-IN") {
    val writer = new ProseWriter(printWriter, layout40)
    val aDecl = TlaOperDecl("LAMBDA", List(OperParam("x")), NameEx("x"))
    val expr = letIn(NameEx("LAMBDA"), aDecl)
    writer.write(expr)
    printWriter.flush()
    val expected =
      """LAMBDA x: x""".stripMargin
    assert(expected == stringWriter.toString)
  }

  test("nested lambdas") {
    // A(LAMBDA x: A(LAMBDA y: y, x), z)
    val writer = new ProseWriter(printWriter, layout40)
    // A(LAMBDA y: y + 1, x)
    val innerDecl =
      TlaOperDecl("LAMBDA", List(OperParam("y")), tla.name("y"))
    val innerLambda = tla.letIn(tla.name("LAMBDA"), innerDecl)
    val innerA = tla.appOp(tla.name("A"), innerLambda, tla.name("x"))
    // A(LAMBDA x: A(LAMBDA y: y + 1, x), z)
    val outerDecl =
      TlaOperDecl("LAMBDA", List(OperParam("x")), innerA)
    val outerLambda = letIn(NameEx("LAMBDA"), outerDecl)
    val outerA = tla.appOp(tla.name("A"), outerLambda, tla.name("z"))
    writer.write(outerA)
    printWriter.flush()
    val expected =
      """A(LAMBDA x: A(LAMBDA y: y, x), z)""".stripMargin
    assert(expected == stringWriter.toString)
  }

  test("a one-line operator declaration") {
    val writer = new ProseWriter(printWriter, layout40)
    val body =
      OperEx(TlaArithOper.plus, ValEx(TlaInt(1)), NameEx("x"))

    val fDecl = TlaOperDecl(
        "A",
        List(OperParam("x")),
        body,
    ) ///
    writer.write(fDecl)
    printWriter.flush()
    val expected =
      """
        |```
        |Define A(x) as 1 + x
        |```
        |
        |""".stripMargin
    assert(expected == stringWriter.toString)
  }

  test("a recursive operator declaration") {
    val writer = new ProseWriter(printWriter, layout40)
    val body =
      OperEx(TlaArithOper.plus, ValEx(TlaInt(1)), OperEx(TlaOper.apply, NameEx("A"), NameEx("x")))

    val fDecl = TlaOperDecl(
        "A",
        List(OperParam("x")),
        body,
    ) ///
    fDecl.isRecursive = true

    writer.write(fDecl)
    printWriter.flush()
    val expected =
      """
        |```
        |Define recursive A(x) as 1 + A(x)
        |```
        |
        |""".stripMargin
    assert(expected == stringWriter.toString)
  }

  test("a recursive operator declaration in LET-IN") {
    val writer = new ProseWriter(printWriter, layout40)
    val body =
      OperEx(TlaArithOper.plus, ValEx(TlaInt(1)), OperEx(TlaOper.apply, NameEx("A"), NameEx("x")))

    val fDecl = TlaOperDecl(
        "A",
        List(OperParam("x")),
        body,
    ) ///
    fDecl.isRecursive = true

    val letInEx = letIn(OperEx(TlaOper.apply, NameEx("A"), ValEx(TlaInt(1))), fDecl)

    writer.write(letInEx)
    printWriter.flush()
    // Igor: I would prefer to have an actual line-break between the recursive signature and the operator definition.
    // However, it is not clear to me how to enforce that in the pretty printer that we are using.
    val expected =
      """Let recursive A(x) be 1 + A(x) in A(1)""".stripMargin
    assert(expected == stringWriter.toString)
  }

  test("a one-line recursive function in LET-IN") {
    val writer = new ProseWriter(printWriter, layout40)
    val recFun =
      OperEx(TlaFunOper.recFunDef,
          OperEx(TlaArithOper.plus, ValEx(TlaInt(1)),
              OperEx(TlaFunOper.app, OperEx(TlaFunOper.recFunRef), NameEx("x"))), NameEx("x"), NameEx("S"))
    val fDecl = TlaOperDecl(
        "f",
        List(),
        recFun,
    ) ///
    val expr = letIn(appDecl(fDecl), fDecl)
    writer.write(expr)
    printWriter.flush()
    val expected =
      """Let recursive function
        |  f[x in S] be
        |  1 + f[x]
        |in
        |f""".stripMargin
    assert(expected == stringWriter.toString)
  }

  test("a one-line recursive function declaration") {
    val writer = new ProseWriter(printWriter, layout40)
    val recFun =
      OperEx(TlaFunOper.recFunDef,
          OperEx(TlaArithOper.plus, ValEx(TlaInt(1)),
              OperEx(TlaFunOper.app, OperEx(TlaFunOper.recFunRef), NameEx("x"))), NameEx("x"), NameEx("S"))
    val fDecl = TlaOperDecl(
        "f",
        List(),
        recFun,
    ) ///
    writer.write(fDecl)
    printWriter.flush()
    val expected =
      """Define recursive function
        |  f[x in S] as
        |  1 + f[x]
        |
        |""".stripMargin
    assert(expected == stringWriter.toString)
  }

  test("declaration of a recursive function of two arguments") {
    val writer = new ProseWriter(printWriter, layout40)
    val body = tla.appFun(tla.recFunRef(), tla.tuple(tla.name("y"), tla.name("x")))
    val recFun =
      tla.recFunDef(body, tla.name("x"), tla.name("S"), tla.name("y"), tla.name("S"))

    val fDecl = TlaOperDecl("f", List(), recFun)
    writer.write(fDecl)
    printWriter.flush()
    val expected =
      """Define recursive function
        |  f[x in S, y in S] as
        |  f[y, x]
        |
        |""".stripMargin
    assert(expected == stringWriter.toString)
  }

  test("constant declaration") {
    val writer = new ProseWriter(printWriter, layout40)
    writer.write(TlaConstDecl("N"))
    printWriter.flush()
    val expected =
      """
        |```
        |Given constant N
        |```
        |
        |""".stripMargin
    assert(expected == stringWriter.toString)
  }

  test("annotated constant declaration") {
    val annotator = new TlaDeclAnnotator {
      override def apply(layout: TextLayout)(decl: TlaDecl): Option[List[String]] = {
        Some(List("aaaa"))
      }
    }

    val writer = new ProseWriter(printWriter, layout40, annotator)
    writer.write(TlaConstDecl("N"))
    printWriter.flush()
    val expected =
      """
        |aaaa
        |
        |```
        |Given constant N
        |```
        |
        |""".stripMargin
    assert(expected == stringWriter.toString)
  }

  test("variable declaration") {
    val writer = new ProseWriter(printWriter, layout40)
    writer.write(TlaVarDecl("x"))
    printWriter.flush()
    val expected =
      """
        |```
        |Introduce state variable x
        |```
        |
        |""".stripMargin
    assert(expected == stringWriter.toString)
  }

  test("assumption") {
    val writer = new ProseWriter(printWriter, layout40)
    writer.write(TlaAssumeDecl(gt(name("N"), int(3))))
    printWriter.flush()
    val expected =
      """
        |```
        |Assume that N > 3
        |```
        |
        |""".stripMargin
    assert(expected == stringWriter.toString)
  }

}
