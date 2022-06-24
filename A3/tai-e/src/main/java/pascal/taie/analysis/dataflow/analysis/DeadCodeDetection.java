/*
 * Tai-e: A Static Analysis Framework for Java
 *
 * Copyright (C) 2022 Tian Tan <tiantan@nju.edu.cn>
 * Copyright (C) 2022 Yue Li <yueli@nju.edu.cn>
 *
 * This file is part of Tai-e.
 *
 * Tai-e is free software: you can redistribute it and/or modify
 * it under the terms of the GNU Lesser General Public License
 * as published by the Free Software Foundation, either version 3
 * of the License, or (at your option) any later version.
 *
 * Tai-e is distributed in the hope that it will be useful,but WITHOUT
 * ANY WARRANTY; without even the implied warranty of MERCHANTABILITY
 * or FITNESS FOR A PARTICULAR PURPOSE. See the GNU Lesser General
 * Public License for more details.
 *
 * You should have received a copy of the GNU Lesser General Public
 * License along with Tai-e. If not, see <https://www.gnu.org/licenses/>.
 */

package pascal.taie.analysis.dataflow.analysis;

import pascal.taie.analysis.MethodAnalysis;
import pascal.taie.analysis.dataflow.analysis.constprop.CPFact;
import pascal.taie.analysis.dataflow.analysis.constprop.ConstantPropagation;
import pascal.taie.analysis.dataflow.analysis.constprop.Value;
import pascal.taie.analysis.dataflow.fact.DataflowResult;
import pascal.taie.analysis.dataflow.fact.SetFact;
import pascal.taie.analysis.graph.cfg.CFG;
import pascal.taie.analysis.graph.cfg.CFGBuilder;
import pascal.taie.analysis.graph.cfg.Edge;
import pascal.taie.config.AnalysisConfig;
import pascal.taie.ir.IR;
import pascal.taie.ir.exp.*;
import pascal.taie.ir.stmt.AssignStmt;
import pascal.taie.ir.stmt.If;
import pascal.taie.ir.stmt.Stmt;
import pascal.taie.ir.stmt.SwitchStmt;

import java.util.*;

public class DeadCodeDetection extends MethodAnalysis {

    public static final String ID = "deadcode";

    public DeadCodeDetection(AnalysisConfig config) {
        super(config);
    }

    @Override
    public Set<Stmt> analyze(IR ir) {
        // obtain CFG
        CFG<Stmt> cfg = ir.getResult(CFGBuilder.ID);
        // obtain result of constant propagation
        DataflowResult<Stmt, CPFact> constants =
                ir.getResult(ConstantPropagation.ID);
        // obtain result of live variable analysis
        DataflowResult<Stmt, SetFact<Var>> liveVars =
                ir.getResult(LiveVariableAnalysis.ID);
        // keep statements (dead code) sorted in the resulting set
        Set<Stmt> deadCode = new TreeSet<>(Comparator.comparing(Stmt::getIndex));
        Set<Stmt> liveCode = new TreeSet<>(Comparator.comparing(Stmt::getIndex));

        Queue<Stmt> stmtQueue = new LinkedList<>();

        // Your task is to recognize dead code in ir and add it to deadCode
        stmtQueue.add(cfg.getEntry());
        while (!stmtQueue.isEmpty()) {
            Stmt stmt = stmtQueue.poll();
//            System.out.println("Parsing Stmt: " + stmt);
            if (cfg.isExit(stmt)) {
                liveCode.add(stmt);
                continue;
            }
            if (deadCode.contains(stmt) || liveCode.contains(stmt)) {
                continue;
            }

            if (stmt instanceof AssignStmt<?,?> assignStmt) {
//                System.out.println("ASSIGNSTMT: " + stmt);
//                System.out.println(liveVars.getOutFact(stmt));
                if (hasNoSideEffect(assignStmt.getRValue()) && assignStmt.getLValue() instanceof Var lVar &&
                        !liveVars.getOutFact(assignStmt).contains(lVar)){
                    deadCode.add(stmt);
                }
                else {
                    liveCode.add(stmt);
                }
//                if (liveVars.getOutFact(stmt).contains((Var)((AssignStmt<?, ?>) stmt).getLValue())) {
////                    System.out.println("Add livecode: " + stmt);
//                    liveCode.add(stmt);
//                }
//                else {
//                    if (hasNoSideEffect(((AssignStmt<?, ?>) stmt).getRValue())) {
//                        deadCode.add(stmt);
//                    }
//                    else {
//                        liveCode.add(stmt);
//                    }
//                }
                stmtQueue.addAll(cfg.getSuccsOf(stmt));
            }
            else if (stmt instanceof If) {
                liveCode.add(stmt);

                Value condition_value = ConstantPropagation.evaluate(((If) stmt).getCondition(),
                        constants.getInFact(stmt));
                if (condition_value.isConstant()) {
                    if (condition_value.getConstant() == 0) {
                        // Mark the If-False block as live code
                        for (Edge<Stmt> e : cfg.getOutEdgesOf(stmt)) {
                            if (e.getKind() == Edge.Kind.IF_FALSE) {
//                                System.out.println("==>" + stmt);
                                stmtQueue.add(e.getTarget());
                                break;
                            }
                        }
                    }
                    else {
                        // Mark the If-True block as live code
                        for (Edge<Stmt> e : cfg.getOutEdgesOf(stmt)) {
                            if (e.getKind() == Edge.Kind.IF_TRUE) {
//                                System.out.println("==>" + stmt);
                                stmtQueue.add(e.getTarget());
                                break;
                            }
                        }
                    }
                }
                else {
                    //                        System.out.println("==>" + stmt);
                    stmtQueue.addAll(cfg.getSuccsOf(stmt));
                }
            }
            else if (stmt instanceof SwitchStmt) {
                liveCode.add(stmt);

                Value condition_value = ConstantPropagation.evaluate(((SwitchStmt) stmt).getVar(),
                        constants.getInFact(stmt));
                if (condition_value.isConstant()) {
                    if (((SwitchStmt) stmt).getCaseValues().contains(condition_value.getConstant())) {
                        for (Edge<Stmt> e : cfg.getOutEdgesOf(stmt)) {
                            if (e.isSwitchCase() && e.getCaseValue() == condition_value.getConstant()) {
//                            System.out.println("==>" + stmt);
                                stmtQueue.add(e.getTarget());
//                            break;
                            }
                        }
                    }
                    else {
//                        System.out.println("==>" + stmt);
                        stmtQueue.add(((SwitchStmt) stmt).getDefaultTarget());
                    }
                }
                else {
                    stmtQueue.addAll(cfg.getSuccsOf(stmt));
                }
            }
            else {
                liveCode.add(stmt);
                stmtQueue.addAll(cfg.getSuccsOf(stmt));
            }
        }

        for (Stmt s : cfg.getIR().getStmts()) {
//        for (Stmt s : cfg) {
            if (!liveCode.contains(s)) {
                deadCode.add(s);
            }
        }

        deadCode.remove(cfg.getEntry());
        deadCode.remove(cfg.getExit());
        return deadCode;
    }

    /**
     * @return true if given RValue has no side effect, otherwise false.
     */
    private static boolean hasNoSideEffect(RValue rvalue) {
        // new expression modifies the heap
        if (rvalue instanceof NewExp ||
                // cast may trigger ClassCastException
                rvalue instanceof CastExp ||
                // static field access may trigger class initialization
                // instance field access may trigger NPE
                rvalue instanceof FieldAccess ||
                // array access may trigger NPE
                rvalue instanceof ArrayAccess) {
            return false;
        }
        if (rvalue instanceof ArithmeticExp) {
            ArithmeticExp.Op op = ((ArithmeticExp) rvalue).getOperator();
            // may trigger DivideByZeroException
            return op != ArithmeticExp.Op.DIV && op != ArithmeticExp.Op.REM;
        }
        return true;
    }
}
