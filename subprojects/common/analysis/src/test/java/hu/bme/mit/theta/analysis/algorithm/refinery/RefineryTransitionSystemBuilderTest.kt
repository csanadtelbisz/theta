/*
 *  Copyright 2025 Budapest University of Technology and Economics
 *
 *  Licensed under the Apache License, Version 2.0 (the "License");
 *  you may not use this file except in compliance with the License.
 *  You may obtain a copy of the License at
 *
 *      http://www.apache.org/licenses/LICENSE-2.0
 *
 *  Unless required by applicable law or agreed to in writing, software
 *  distributed under the License is distributed on an "AS IS" BASIS,
 *  WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied.
 *  See the License for the specific language governing permissions and
 *  limitations under the License.
 */

package hu.bme.mit.theta.analysis.algorithm.refinery

import hu.bme.mit.theta.common.dsl.Env
import hu.bme.mit.theta.common.dsl.Symbol
import hu.bme.mit.theta.common.dsl.SymbolTable
import hu.bme.mit.theta.core.decl.Decl
import hu.bme.mit.theta.core.decl.Decls
import hu.bme.mit.theta.core.stmt.Stmt
import hu.bme.mit.theta.core.type.inttype.IntExprs.Int
import hu.bme.mit.theta.core.utils.StmtUtils
import hu.bme.mit.theta.grammar.dsl.SimpleScope
import hu.bme.mit.theta.grammar.dsl.stmt.StatementWrapper
import org.junit.jupiter.api.Assertions.assertEquals
import org.junit.jupiter.params.ParameterizedTest
import org.junit.jupiter.params.provider.Arguments
import org.junit.jupiter.params.provider.MethodSource

class RefineryTransitionSystemBuilderTest {

  companion object {

    private const val UNSUPPORTED_EMPTY_ACTION = "<UNSUPPORTED EMPTY>"

    private data class NamedSymbol(private val _name: String) : Symbol {

      override fun getName(): String = _name
    }

    private fun getRefineryRuleBuilder(pointers: Set<Decl<*>>): RefineryTransitionRuleBuilder<Stmt> =
      object : RefineryTransitionRuleBuilder<Stmt>(variables = mutableSetOf(), pointers = pointers) {
        private var counter = 0

        override fun build(transition: Stmt): List<RefineryRule> =
          transition.toRules("transition${counter++}").map {
            val rule =
              if (it.actionClauses.isEmpty()) it.copy(actionClauses = listOf(UNSUPPORTED_EMPTY_ACTION))
              else it
            rule.toRefineryRule()
          }
      }

    private data class RefineryRuleBuilderTestData(
      val stmt: String,
      val expectedRules: List<String>,
      val pointers: Set<String> = setOf(),
      val expectedException: Throwable? = null,
    ) : Arguments {

      override fun get(): Array<Any> =
        Arguments.of(stmt, expectedRules, pointers, expectedException).get()
    }

    @JvmStatic
    private fun data(): Collection<RefineryRuleBuilderTestData> =
      listOf(
        RefineryRuleBuilderTestData(
          "skip",
          listOf(
            """
            |rule transition0_0() <->
            |    true
            |==>
            |    $UNSUPPORTED_EMPTY_ACTION.
            """.trimMargin()
          ),
        ),

        RefineryRuleBuilderTestData(
          "(assign v 1)",
          listOf(
            """
            |rule transition0_0() <->
            |    true
            |==>
            |    v(env): 1.
            """.trimMargin()
          ),
        ),

        RefineryRuleBuilderTestData(
          "(assume (not (= v1 v2)))",
          listOf(
            """
            |rule transition0_0() <->
            |    !(v1(env) == v2(env))
            |==>
            |    $UNSUPPORTED_EMPTY_ACTION.
            """.trimMargin()
          ),
        ),

        RefineryRuleBuilderTestData(
          "(assume (not (= (deref p 0 Int) 3)))",
          listOf(
            """
            |rule transition0_0() <->
            |    name(p) == "p",
            |    target(p, base_0),
            |    object(base_0, pointed_0),
            |    !(value(pointed_0) == 3)
            |==>
            |    $UNSUPPORTED_EMPTY_ACTION.
            """.trimMargin()
          ),
          setOf("p"),
        ),

        RefineryRuleBuilderTestData(
          "(assign v (deref p 1 Int))",
          listOf(
            """
            |rule transition0_0(Value pointed_0) <->
            |    name(p) == "p",
            |    target(p, base_0),
            |    parts(region_0, base_0),
            |    parts(region_0, referenced_0),
            |    offset(referenced_0) == offset(base_0) + (1),
            |    object(referenced_0, pointed_0)
            |==>
            |    v(env): value(pointed_0).
            """.trimMargin()
          ),
          setOf("p"),
        ),

        RefineryRuleBuilderTestData(
          "(assume (= (deref (deref p 1 Int) 2 Int) 3))",
          listOf(
            """
            |rule transition0_0() <->
            |    name(p) == "p",
            |    target(p, base_1),
            |    parts(region_1, base_1),
            |    parts(region_1, referenced_1),
            |    offset(referenced_1) == offset(base_1) + (1),
            |    object(referenced_1, pointed_1),
            |    target(pointed_1, base_0),
            |    parts(region_0, base_0),
            |    parts(region_0, referenced_0),
            |    offset(referenced_0) == offset(base_0) + (2),
            |    object(referenced_0, pointed_0),
            |    value(pointed_0) == 3
            |==>
            |    $UNSUPPORTED_EMPTY_ACTION.
            """.trimMargin()
          ),
          setOf("p"),
        ),

        RefineryRuleBuilderTestData(
          "(memassign (deref p 1 Int) 5)",
          listOf(
            """
            |rule transition0_0(Value pointed_0) <->
            |    name(p) == "p",
            |    target(p, base_0),
            |    parts(region_0, base_0),
            |    parts(region_0, referenced_0),
            |    offset(referenced_0) == offset(base_0) + (1),
            |    object(referenced_0, pointed_0)
            |==>
            |    value(pointed_0): 5.
            """.trimMargin()
          ),
          setOf("p"),
        ),

        RefineryRuleBuilderTestData(
          "(assume (= (deref v 0 Int) p)))",
          listOf(),
          setOf("p"),
          IllegalStateException("Pointer expression expected at (deref v 0 Int), expression v does not yield a pointer expression.")
        ),
      )

    private val symbols = listOf(
      NamedSymbol("v") to Decls.Var("v", Int()),
      NamedSymbol("v1") to Decls.Var("v1", Int()),
      NamedSymbol("v2") to Decls.Var("v2", Int()),
      NamedSymbol("p") to Decls.Var("p", Int()),
    )
  }

  @ParameterizedTest
  @MethodSource("data")
  fun testRefineryRuleBuilder(
    stmtStr: String,
    expectedRules: List<String>,
    pointers: Set<String>,
    expectedException: Throwable?,
  ) {
    println("Testing statement: $stmtStr with pointers: $pointers")
    val symbolTable = SymbolTable()
    val env = Env()
    for ((symbol, decl) in symbols) {
      symbolTable.add(symbol)
      env.define(symbol, decl)
    }
    val scope = SimpleScope(symbolTable)

    val stmt = StatementWrapper(stmtStr, scope).instantiate(env)

    val vars = StmtUtils.getVars(stmt)
    val builder = getRefineryRuleBuilder(
      pointers.map { p -> vars.first { it.name == p } }.toSet()
    )

    val rules =
      try {
        builder.build(stmt)
      } catch (e: Throwable) {
        if (expectedException != null) {
          assertEquals(expectedException::class, e::class)
          assertEquals(expectedException.message, e.message)
          return
        }
        throw e
      }

    assertEquals(expectedRules.size, rules.size)
    rules.forEachIndexed { index, rule ->
      assertEquals(expectedRules[index].trim(), rule.toString().trim())
    }
  }
}