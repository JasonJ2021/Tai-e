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

package pascal.taie.analysis.dataflow.inter;

import pascal.taie.analysis.dataflow.analysis.constprop.CPFact;
import pascal.taie.analysis.dataflow.analysis.constprop.ConstantPropagation;
import pascal.taie.analysis.dataflow.analysis.constprop.Value;
import pascal.taie.analysis.graph.cfg.CFG;
import pascal.taie.analysis.graph.cfg.CFGBuilder;
import pascal.taie.analysis.graph.icfg.CallEdge;
import pascal.taie.analysis.graph.icfg.CallToReturnEdge;
import pascal.taie.analysis.graph.icfg.NormalEdge;
import pascal.taie.analysis.graph.icfg.ReturnEdge;
import pascal.taie.config.AnalysisConfig;
import pascal.taie.ir.IR;
import pascal.taie.ir.exp.InvokeExp;
import pascal.taie.ir.exp.LValue;
import pascal.taie.ir.exp.RValue;
import pascal.taie.ir.exp.Var;
import pascal.taie.ir.stmt.Invoke;
import pascal.taie.ir.stmt.Stmt;
import pascal.taie.language.classes.JMethod;

import java.util.List;

/**
 * Implementation of interprocedural constant propagation for int values.
 */
public class InterConstantPropagation extends
        AbstractInterDataflowAnalysis<JMethod, Stmt, CPFact> {

    public static final String ID = "inter-constprop";

    private final ConstantPropagation cp;

    public InterConstantPropagation(AnalysisConfig config) {
        super(config);
        cp = new ConstantPropagation(new AnalysisConfig(ConstantPropagation.ID));
    }

    @Override
    public boolean isForward() {
        return cp.isForward();
    }

    @Override
    public CPFact newBoundaryFact(Stmt boundary) {
        IR ir = icfg.getContainingMethodOf(boundary).getIR();
        return cp.newBoundaryFact(ir.getResult(CFGBuilder.ID));
    }

    @Override
    public CPFact newInitialFact() {
        return cp.newInitialFact();
    }

    @Override
    public void meetInto(CPFact fact, CPFact target) {
        cp.meetInto(fact, target);
    }

    @Override
    protected boolean transferCallNode(Stmt stmt, CPFact in, CPFact out) {
        // TODO - finish me
//        return out.copyFrom(in);
        CPFact Copy = out.copy();
        for (Var key : in.keySet()) {
            out.update(key, in.get(key));
        }
        return !out.equals(Copy);
    }

    @Override
    protected boolean transferNonCallNode(Stmt stmt, CPFact in, CPFact out) {
        // TODO - finish me
        return cp.transferNode(stmt, in, out);
    }

    @Override
    protected CPFact transferNormalEdge(NormalEdge<Stmt> edge, CPFact out) {
        // TODO - finish me
        return out.copy();
    }

    @Override
    protected CPFact transferCallToReturnEdge(CallToReturnEdge<Stmt> edge, CPFact out) {
        // TODO - finish me
        CPFact out_copy = out.copy();
        if (edge.getSource().getDef().isPresent()) {
            LValue lValue = edge.getSource().getDef().get();
            if(lValue instanceof Var){
                out.remove((Var) lValue);
            }
        }
        return out;
    }

    @Override
    protected CPFact transferCallEdge(CallEdge<Stmt> edge, CPFact callSiteOut) {
        // TODO - finish me
        CPFact cpfact = new CPFact();
        // 1.首先我们要拿到invokeExp
        InvokeExp invokeExp = null;
        for (RValue rvalue : edge.getSource().getUses()) {
            if (rvalue instanceof InvokeExp) {
                invokeExp = (InvokeExp) rvalue;
                break;
            }
        }
        if (invokeExp == null) return null;
        // 2.在callee Jmethod中拿到形参
        for (int i = 0; i < edge.getCallee().getParamCount(); i++) {
            Var param = edge.getCallee().getIR().getParam(i);
            // 3. 把形参和实参的value对应起来
            Value value = callSiteOut.get(invokeExp.getArg(i));
            cpfact.update(param, value);
        }

        return cpfact;
    }

    @Override
    protected CPFact transferReturnEdge(ReturnEdge<Stmt> edge, CPFact returnOut) {
        // TODO - finish me
        CPFact cpFact = new CPFact();
        // 如果callsite左侧没有变量赋值，那么直接返回一个空的cpfact
        if (edge.getCallSite().getDef().isEmpty()) {
            return cpFact;
        }
        // 获取定义变量
        LValue def_Var = edge.getCallSite().getDef().get();
//        if (edge.getReturnVars().size() == 1) {
//            cpFact.update((Var) def_Var, returnOut.get(edge.getReturnVars().iterator().next()));
//        } else {
//            cpFact.update((Var) def_Var, Value.getNAC());
//        }
        // 如果有多个返回值，需要进行Meet操作
        // === Sol ===
        Value[] values = new Value[1];
        values[0] = Value.getUndef();
        edge.getReturnVars().stream().forEach(Var -> {
            Value value = returnOut.get(Var);
            values[0] = cp.meetValue(value , values[0]);
        });
        cpFact.update((Var)def_Var , values[0]);
        return cpFact;
    }
}
