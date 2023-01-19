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

import pascal.taie.World;
import pascal.taie.analysis.dataflow.analysis.constprop.CPFact;
import pascal.taie.analysis.dataflow.analysis.constprop.ConstantPropagation;
import pascal.taie.analysis.dataflow.analysis.constprop.Value;
import pascal.taie.analysis.graph.cfg.CFG;
import pascal.taie.analysis.graph.cfg.CFGBuilder;
import pascal.taie.analysis.graph.icfg.CallEdge;
import pascal.taie.analysis.graph.icfg.CallToReturnEdge;
import pascal.taie.analysis.graph.icfg.NormalEdge;
import pascal.taie.analysis.graph.icfg.ReturnEdge;
import pascal.taie.analysis.pta.PointerAnalysisResult;
import pascal.taie.analysis.pta.core.cs.element.InstanceField;
import pascal.taie.analysis.pta.core.heap.Obj;
import pascal.taie.config.AnalysisConfig;
import pascal.taie.ir.IR;
import pascal.taie.ir.exp.*;
import pascal.taie.ir.stmt.*;
import pascal.taie.language.classes.JField;
import pascal.taie.language.classes.JMethod;

import java.util.HashMap;
import java.util.HashSet;
import java.util.Map;
import java.util.Set;
import java.util.stream.Collectors;

import static pascal.taie.analysis.dataflow.analysis.constprop.ConstantPropagation.canHoldInt;

/**
 * Implementation of interprocedural constant propagation for int values.
 */
public class InterConstantPropagation extends
        AbstractInterDataflowAnalysis<JMethod, Stmt, CPFact> {

    public static final String ID = "inter-constprop";

    private final ConstantPropagation cp;
    private PointerAnalysisResult pta;
    private Map<Var, Set<Stmt>> storeFields;
    private Map<Var, Set<Stmt>> storeArrays;

    public InterConstantPropagation(AnalysisConfig config) {
        super(config);
        cp = new ConstantPropagation(new AnalysisConfig(ConstantPropagation.ID));
    }

    @Override
    protected void initialize() {
        String ptaId = getOptions().getString("pta");
        pta = World.get().getResult(ptaId);
        // You can do initialization work here
        // 维护别名信息
        storeFields = new HashMap<>();
        storeArrays = new HashMap<>();
        for (Var var_x : pta.getVars()) {
            storeFields.put(var_x, new HashSet<>());
            storeArrays.put(var_x, new HashSet<>());
            for (Var var_y : pta.getVars()) {
                for (Obj obj : pta.getPointsToSet(var_x)) {
                    // 如果var_y指向的对象集合中包含var_x指向的对象集合，那么他们是一对别名
                    // 需要把别名的storefield/storeArray存放起来
                    if (pta.getPointsToSet(var_y).contains(obj)) {
                        storeFields.get(var_x).addAll(var_y.getStoreFields());
                        storeArrays.get(var_x).addAll(var_y.getStoreArrays());
                        break;
                    }
                }
            }
        }
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
        return out.copyFrom(in);
    }

    @Override
    protected boolean transferNonCallNode(Stmt stmt, CPFact in, CPFact out) {
        // TODO - finish me
        if (stmt instanceof LoadField loadField) {
            // 先处理字段 x = y.f / T.f
            Var lValue = loadField.getLValue(); // x
            if (!canHoldInt(lValue)) {
                return out.copyFrom(in);
            }
            JField jField = loadField.getRValue().getFieldRef().resolve();
            if (loadField.isStatic()) {
                // 处理静态字段
                // 获得T.f中T的所有storeField rvalue ,meet之后赋值给左边的x
                Set<Value> _set = new HashSet<>();
                for (Stmt node : icfg) {
                    if (node instanceof StoreField storeField && storeField.isStatic()) {
                        JField resolve = storeField.getFieldAccess().getFieldRef().resolve();
                        if (resolve == jField) {
                            Var rValue = storeField.getRValue();
                            Value value = solver.getResult().getInFact(storeField).get(rValue);
                            _set.add(value); // 添加到set中
                        }
                    }
                }
                // 现在需要对set中的value进行一个meet操作
                Value res = Value.getUndef();
                for (Value value : _set) {
                    res = cp.meetValue(res, value);
                }
                CPFact in_copy = in.copy();
                in_copy.remove(lValue);
                in_copy.update(lValue, res);
                return out.copyFrom(in_copy);
            } else {
                // 处理实例字段 x = y.f
                // 如果z.f是y.f的别名，需要把z.f的storeField也考虑进来
                assert loadField.getFieldAccess() instanceof InstanceFieldAccess;
                Var base = ((InstanceFieldAccess) loadField.getFieldAccess()).getBase();
                // 在base的别名storeField中寻找 base.Field = xxx , Field要和jField相同
                Set<StoreField> store_to_field = storeFields.get(base).stream()
                        .map(storefield -> (StoreField) storefield).filter(storefield -> storefield.getFieldRef().resolve() == jField)
                        .collect(Collectors.toSet());
                Set<Value> _set = new HashSet<>();
                Value res = Value.getUndef();
                for (StoreField storeField : store_to_field) {
                    Var rValue = storeField.getRValue();
                    Value value = solver.getResult().getInFact(storeField).get(rValue);
                    _set.add(value);
                }
                for (Value value : _set) {
                    res = cp.meetValue(res, value);
                }
                CPFact in_copy = in.copy();
                in_copy.remove(lValue);
                in_copy.update(lValue, res);
                return out.copyFrom(in_copy);
            }
        } else if (stmt instanceof LoadArray loadArray) {
            // 处理数组 x = a[i]
            Var lValue = loadArray.getLValue(); // x
            if (!canHoldInt(lValue)) {
                return out.copyFrom(in);
            }
            ArrayAccess arrayAccess = loadArray.getArrayAccess();
            if (solver.getResult().getInFact(stmt).get(arrayAccess.getIndex()) == Value.getUndef()) {
                // a[i] , i == UNDEF，没有别名
                CPFact in_copy = in.copy();
                in_copy.update(lValue, Value.getUndef());
                return out.copyFrom(in_copy);
            }
            Set<StoreArray> collects = storeArrays.get(arrayAccess.getBase()).stream()
                    .map(storearray -> (StoreArray) storearray)
                    .filter(storeArray -> solver.getResult().getInFact(storeArray).get(storeArray.getArrayAccess().getIndex()) != Value.getUndef())
                    .filter(storearray -> solver.getResult().getInFact(stmt).get(arrayAccess.getIndex()) == Value.getNAC() ||
                            solver.getResult().getInFact(storearray).get(storearray.getArrayAccess().getIndex()) == Value.getNAC() ||
                            solver.getResult().getInFact(storearray).get(storearray.getArrayAccess().getIndex()) == solver.getResult().getInFact(stmt).get(arrayAccess.getIndex())
                    ).collect(Collectors.toSet());
            Set<Value> _set = new HashSet<>();
            Value res = Value.getUndef();
            for (StoreArray storeArray : collects) {
                Var rValue = storeArray.getRValue();
                Value value = solver.getResult().getInFact(storeArray).get(rValue);
                _set.add(value);
            }
            for (Value value : _set) {
                res = cp.meetValue(res, value);
            }
            CPFact in_copy = in.copy();
            in_copy.remove(lValue);
            in_copy.update(lValue, res);
            return out.copyFrom(in_copy);
        }

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
            if (lValue instanceof Var) {
                out_copy.remove((Var) lValue); // 这里一开始写了out.remove.......
            }
        }
        return out_copy;
    }

    @Override
    protected CPFact transferCallEdge(CallEdge<Stmt> edge, CPFact callSiteOut) {
        // TODO - finish me
        CPFact cpfact = new CPFact();
        // 1.首先我们要拿到invokeExp
        Invoke invoke = (Invoke) edge.getSource();
        InvokeExp invokeExp = invoke.getInvokeExp();

        // 2.在callee Jmethod中拿到形参
        for (int i = 0; i < edge.getCallee().getParamCount(); i++) {
            Var param = edge.getCallee().getIR().getParam(i);
            // 3. 把形参和实参的value对应起来
            Value value = callSiteOut.get(invokeExp.getArg(i));
            if (canHoldInt(param)) cpfact.update(param, value);
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
//        LValue def_Var = edge.getCallSite().getDef().get();
        Invoke invoke = (Invoke) edge.getCallSite();
        Var def_Var = invoke.getLValue();
        if (def_Var == null) return cpFact;
        // 如果有多个返回值，需要进行Meet操作
        // === Sol ===
        Value[] values = new Value[1];
        values[0] = Value.getUndef();
        edge.getReturnVars().forEach(var -> {
            Value value = returnOut.get(var);
            values[0] = cp.meetValue(value, values[0]);
        });
        cpFact.update(def_Var, values[0]);
        return cpFact;
    }
}
