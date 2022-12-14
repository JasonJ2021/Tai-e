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
import pascal.taie.util.collection.Pair;

import java.util.*;

import static pascal.taie.analysis.dataflow.analysis.LiveVariableAnalysis.*;

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
        // TODO - finish me
        // Your task is to recognize dead code in ir and add it to deadCode
        // 先一个一个分析，不考虑效率问题
        // 2.1.1 控制流不可达代码分析.
        // 从entry开始遍历语句
        Set<Stmt> reachable = new HashSet<>();
        Set<Stmt> control_flow_unreachable = new HashSet<>();
        for (Stmt stmt : cfg) {
            if(stmt.getLineNumber() < 0)continue;
            control_flow_unreachable.add(stmt);
        }
        Deque<Stmt> deque = new ArrayDeque<>();
        deque.addLast(cfg.getEntry());
        while (!deque.isEmpty()) {
            Stmt stmt = deque.removeFirst();
            if(reachable.contains(stmt))continue;
            reachable.add(stmt);
            control_flow_unreachable.remove(stmt);
            if (cfg.isExit(stmt)) continue;
            for (Edge<Stmt> succ_edge : cfg.getOutEdgesOf(stmt)) {
                deque.addLast(succ_edge.getTarget());
            }
        }
        deadCode.addAll(control_flow_unreachable);
        reachable.clear();
        // 2.1.2 分支不可达代码分析
        Set<Stmt> branch_unreachable = new HashSet<>();
        for (Stmt stmt : cfg) {
            if(stmt.getLineNumber() < 0)continue;
            branch_unreachable.add(stmt);
        }
        deque.addLast(cfg.getEntry());
        while (!deque.isEmpty()) {
            Stmt stmt = deque.removeFirst();
            // 防止闭环
            if(reachable.contains(stmt))continue;
            reachable.add(stmt);
            branch_unreachable.remove(stmt);
            if (cfg.isExit(stmt)) continue;
            // 先处理IF的情况
            if (stmt instanceof If) {
                If if_stmt = (If) stmt;
                Value if_value = ConstantPropagation.evaluate(if_stmt.getCondition(), constants.getOutFact(if_stmt));
                if (!if_value.isConstant()) {
                    for (Edge<Stmt> edge : cfg.getOutEdgesOf(stmt)) {
                        deque.addLast(edge.getTarget());
                    }
                } else if (if_value.getConstant() == 1) {
                    // always true
                    for (Edge<Stmt> edge : cfg.getOutEdgesOf(stmt)) {
                        if (edge.getKind() == Edge.Kind.IF_TRUE) {
                            deque.addLast(edge.getTarget());
                        }
                    }
                } else {
                    // always false
                    for (Edge<Stmt> edge : cfg.getOutEdgesOf(stmt)) {
                        if (edge.getKind() == Edge.Kind.IF_FALSE) {
                            deque.addLast(edge.getTarget());
                        }
                    }
                }
            } else if (stmt instanceof SwitchStmt) {
                SwitchStmt switch_stmt = (SwitchStmt) stmt;
                Value switch_value = constants.getOutFact(stmt).get(switch_stmt.getVar());
                if (!switch_value.isConstant()) {
                    for (Edge<Stmt> edge : cfg.getOutEdgesOf(stmt)) {
                        deque.addLast(edge.getTarget());
                    }
                } else {
                    int case_value = switch_value.getConstant();
                    if (!switch_stmt.getCaseValues().contains(case_value)) {
                        // 只能匹配default
                        deque.addLast(switch_stmt.getDefaultTarget());
                    } else {
                        // 从匹配出开始加入target stmt
                        int i = switch_stmt.getCaseValues().indexOf(case_value);
                        List<Pair<Integer, Stmt>> caseTargets = switch_stmt.getCaseTargets();
                        // fall through不需要自己处理，只需要把匹配到的那一行加入到deque中即可
                        deque.addLast(caseTargets.get(i).second());
                    }
                }
            } else {
                // 既不是If也不是switch，
                for (Edge<Stmt> succ_edge : cfg.getOutEdgesOf(stmt)) {
                    deque.addLast(succ_edge.getTarget());
                }
            }
        }
        deadCode.addAll(branch_unreachable);

        // 2.2 无用赋值判断
        for(Stmt stmt : cfg){
            if(stmt instanceof AssignStmt<?, ?> assignStmt){
                Optional<LValue> lhs = assignStmt.getDef();
                RValue rhs = assignStmt.getRValue();
                SetFact<Var> outFact = liveVars.getOutFact(stmt);
                if(lhs.isPresent() && lhs.get() instanceof Var &&!outFact.contains((Var)lhs.get()) && hasNoSideEffect(rhs)){
                    deadCode.add(stmt);
                }
            }
        }

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
