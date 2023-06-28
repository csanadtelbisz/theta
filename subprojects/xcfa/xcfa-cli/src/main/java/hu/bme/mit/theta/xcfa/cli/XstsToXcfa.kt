package hu.bme.mit.theta.xcfa.cli

import hu.bme.mit.theta.core.decl.Decls
import hu.bme.mit.theta.core.decl.VarDecl
import hu.bme.mit.theta.core.stmt.*
import hu.bme.mit.theta.core.type.Expr
import hu.bme.mit.theta.core.type.abstracttype.EqExpr
import hu.bme.mit.theta.core.type.abstracttype.LeqExpr
import hu.bme.mit.theta.core.type.anytype.RefExpr
import hu.bme.mit.theta.core.type.booltype.AndExpr
import hu.bme.mit.theta.core.type.booltype.BoolExprs
import hu.bme.mit.theta.core.type.booltype.BoolLitExpr
import hu.bme.mit.theta.core.type.booltype.BoolType
import hu.bme.mit.theta.core.type.inttype.IntLitExpr
import hu.bme.mit.theta.core.type.inttype.IntType
import hu.bme.mit.theta.core.utils.TypeUtils.cast
import hu.bme.mit.theta.xcfa.model.*
import hu.bme.mit.theta.xcfa.passes.CPasses
import hu.bme.mit.theta.xcfa.passes.ProcedurePassManager
import hu.bme.mit.theta.xsts.XSTS
import java.math.BigInteger

fun getXcfaFromXsts(xsts: XSTS): XCFA {
    val builder = XcfaBuilder("")
    val propertyIsSafe = false

    // Set vars

    (xsts.vars union xsts.varToType.keys).map {
        val initValue = when (it.type) {
            is IntType -> IntLitExpr.of(BigInteger.valueOf(0))
            is BoolType -> BoolLitExpr.of(false)
            else -> throw UnsupportedOperationException("Unsupported XSTS type.")
        }
        XcfaGlobalVar(it, initValue)
    }.forEach(builder::addVar)

    // Transitions to processes

    val passes = CPasses(false)
    xsts.env.stmts.forEachIndexed { envI, env ->
        xsts.tran.stmts.forEachIndexed { tranI, tran ->
            val name = "env${envI}_tran$tranI"
            val procedure = getProcedureBuilder(builder, name, passes)

            val loopLoc = XcfaLocation("${name}_loop")
            procedure.addLoc(loopLoc)
            procedure.addEdge(XcfaEdge(procedure.initLoc, loopLoc, SequenceLabel(listOf())))

            val stmts = (if (env is SkipStmt) tran.flatStmts else env.flatStmts + tran.flatStmts)
                .map { StmtLabel(it, metadata = EmptyMetaData) }.toMutableList()

            procedure.addEdge(XcfaEdge(loopLoc, loopLoc, SequenceLabel(stmts)))
        }
    }

    // Initial assignments

    val initStmts = xsts.initFormula.toXcfaLabels()
    val unassignedVars = builder.getVars().map { it.wrappedVar } subtract
            initStmts.filter { it is StmtLabel && it.stmt is AssignStmt<*> }
                .map { ((it as StmtLabel).stmt as AssignStmt<*>).varDecl }.toSet()
    unassignedVars.forEach { initStmts.add(StmtLabel(stmt = HavocStmt.of(it), metadata = EmptyMetaData)) }

    // Entry procedure

    val procedures = builder.getProcedures().toList()
    val main = getProcedureBuilder(builder, "main", passes, true)
    procedures.forEach { p ->
        val pidVar = Decls.Var("main::thread_${p.name}", IntType.getInstance())
        main.addVar(pidVar)
        initStmts.add(StartLabel(p.name, listOf(), pidVar, EmptyMetaData))
    }
    val endInit = XcfaLocation("main_end_init")
    main.addLoc(endInit)
    main.addEdge(XcfaEdge(main.initLoc, endInit, SequenceLabel(initStmts)))

    main.createErrorLoc()
    if (propertyIsSafe) {
        val errorCond = BoolExprs.Not(BoolExprs.And(builder.getVars().map {
            LeqExpr.create2(it.wrappedVar.ref, IntLitExpr.of(BigInteger.valueOf(1)))
        }))
        val errorLabel = StmtLabel(AssumeStmt.of(errorCond), metadata = EmptyMetaData)
        main.addEdge(XcfaEdge(endInit, main.errorLoc.get(), errorLabel))
    } else {
        val errorLabel = StmtLabel(AssumeStmt.of(BoolExprs.Not(xsts.prop)), metadata = EmptyMetaData)
        main.addEdge(XcfaEdge(endInit, main.errorLoc.get(), errorLabel))
    }

    return builder.build()
}

private fun getProcedureBuilder(builder: XcfaBuilder, name: String, passes: ProcedurePassManager, init: Boolean = false): XcfaProcedureBuilder {
    val procedure = XcfaProcedureBuilder(name, passes)
    if (init) {
        builder.addEntryPoint(procedure, listOf())
    } else {
        builder.addProcedure(procedure)
    }
    val toAdd: VarDecl<*> = Decls.Var(name + "_ret", IntType.getInstance())
    procedure.addParam(toAdd, ParamDirection.OUT)
    procedure.createInitLoc()
    return procedure
}

private fun Expr<BoolType>.toXcfaLabels(): MutableList<XcfaLabel> {
    return when (this) {
        is AndExpr -> ops.flatMap { it.toXcfaLabels() }.toMutableList()

        is EqExpr<*> -> {
            val type = leftOp.type
            mutableListOf(
                StmtLabel(
                    stmt = AssignStmt.of(cast((leftOp as RefExpr).decl as VarDecl<*>, type), cast(rightOp, type)),
                    metadata = EmptyMetaData
                )
            )
        }

        else -> throw UnsupportedOperationException("Unsupported XSTS formula.")
    }
}

private val Stmt.flatStmts: List<Stmt>
    get() = when (this) {
        is SequenceStmt -> stmts
        is NonDetStmt -> throw UnsupportedOperationException("Unflattened XSTS transitions are not supported.")
        else -> listOf(this)
    }
