package hu.bme.mit.theta.xcfa.cli

import hu.bme.mit.theta.core.decl.Decls
import hu.bme.mit.theta.core.decl.VarDecl
import hu.bme.mit.theta.core.stmt.*
import hu.bme.mit.theta.core.type.abstracttype.LeqExpr
import hu.bme.mit.theta.core.type.booltype.BoolExprs
import hu.bme.mit.theta.core.type.booltype.BoolLitExpr
import hu.bme.mit.theta.core.type.booltype.BoolType
import hu.bme.mit.theta.core.type.inttype.IntLitExpr
import hu.bme.mit.theta.core.type.inttype.IntType
import hu.bme.mit.theta.xcfa.model.*
import hu.bme.mit.theta.xcfa.passes.*
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

    val passes = XstsPasses()
    val processes = normalize(SequenceStmt.of(listOf(xsts.env, xsts.tran)))
    processes.labels.forEachIndexed { i, processLabel ->
        val name = "proc$i"
        val procedure = getProcedureBuilder(builder, name, passes)
        val loopLoc = XcfaLocation("${name}_loop")
        procedure.addLoc(loopLoc)
        procedure.addEdge(XcfaEdge(procedure.initLoc, loopLoc, SequenceLabel(listOf())))
        procedure.addEdge(XcfaEdge(loopLoc, loopLoc, processLabel))
    }

    // Entry procedure: initial assignments, init transition

    val procedures = builder.getProcedures().toList()
    val main = getProcedureBuilder(builder, "main", passes, true)
    val initStmts = mutableListOf<XcfaLabel>(StmtLabel(AssumeStmt.of(xsts.initFormula), metadata = EmptyMetaData))
    procedures.forEach { p ->
        val pidVar = Decls.Var("main::thread_${p.name}", IntType.getInstance())
        main.addVar(pidVar)
        initStmts.add(StartLabel(p.name, listOf(), pidVar, EmptyMetaData))
    }
    val endInitFormula = XcfaLocation("main_end_init_formula")
    main.addLoc(endInitFormula)
    main.addEdge(XcfaEdge(main.initLoc, endInitFormula, SequenceLabel(initStmts)))
    val endInit = XcfaLocation("main_end_init")
    main.addLoc(endInit)
    main.addEdge(XcfaEdge(endInitFormula, endInit, normalize(xsts.init)))

    main.createErrorLoc()
    if (propertyIsSafe) {
        val errorCond = BoolExprs.Not(BoolExprs.And(builder.getVars().map {
            LeqExpr.create2(it.wrappedVar.ref, IntLitExpr.of(BigInteger.valueOf(1)))
        }))
        val errorLabel = StmtLabel(AssumeStmt.of(errorCond), metadata = EmptyMetaData)
        main.addEdge(XcfaEdge(endInit, main.errorLoc.get(), SequenceLabel(listOf(errorLabel))))
    } else {
        val errorLabel = StmtLabel(AssumeStmt.of(BoolExprs.Not(xsts.prop)), metadata = EmptyMetaData)
        main.addEdge(XcfaEdge(endInit, main.errorLoc.get(), SequenceLabel(listOf(errorLabel))))
    }

    return builder.build()
}

private fun getProcedureBuilder(builder: XcfaBuilder, name: String, passes: ProcedurePassManager, init: Boolean = false): XcfaProcedureBuilder {
    val procedure = XcfaProcedureBuilder(name, passes)
    procedure.metaData["normal"] = Unit
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

private fun normalize(stmt: Stmt): NondetLabel {
    val collector = mutableListOf<MutableList<XcfaLabel>>()
    collector.add(mutableListOf())
    normalize(stmt, collector)
    return NondetLabel(collector.map { SequenceLabel(it) }.toSet())
}

private fun normalize(stmt: Stmt, collector: MutableList<MutableList<XcfaLabel>>) {
    when (stmt) {
        is SequenceStmt -> stmt.stmts.forEach { normalize(it, collector) }
        is NonDetStmt -> {
            val newCollector = mutableListOf<MutableList<XcfaLabel>>()
            stmt.stmts.forEach { nondetBranch ->
                val copy = collector.copy()
                normalize(nondetBranch, copy)
                newCollector.addAll(copy)
            }
            collector.clear()
            collector.addAll(newCollector)
        }

        is SkipStmt -> {}
        else -> collector.forEach { it.add(StmtLabel(stmt, metadata = EmptyMetaData)) }
    }
}

private fun MutableList<MutableList<XcfaLabel>>.copy() = map { it.toMutableList() }.toMutableList()

private class XstsPasses : ProcedurePassManager(listOf(
    // formatting
    //NormalizePass(),
    DeterministicPass(),
    // removing redundant elements
    EmptyEdgeRemovalPass(),
    UnusedLocRemovalPass(),
    // optimizing
    SimplifyExprsPass(),
    // handling intrinsics
    //ErrorLocationPass(checkOverflow),
    //FinalLocationPass(checkOverflow),
    //SvCompIntrinsicsPass(),
    //FpFunctionsToExprsPass(),
    //PthreadFunctionsPass(),
    LoopUnrollPass(),
    // trying to inline procedures
    //InlineProceduresPass(),
    RemoveDeadEnds(),
    EliminateSelfLoops(),
    // handling remaining function calls
    NondetFunctionPass(),
    LbePass(),
    NormalizePass(), // needed after lbe, TODO
    DeterministicPass(), // needed after lbe, TODO
    HavocPromotionAndRange(),
    // Final cleanup
    UnusedVarPass(),
))
