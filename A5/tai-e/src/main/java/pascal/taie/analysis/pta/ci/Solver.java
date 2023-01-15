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

package pascal.taie.analysis.pta.ci;

import org.apache.logging.log4j.LogManager;
import org.apache.logging.log4j.Logger;
import pascal.taie.World;
import pascal.taie.analysis.graph.callgraph.*;
import pascal.taie.analysis.pta.PointerAnalysisResult;
import pascal.taie.analysis.pta.core.heap.HeapModel;
import pascal.taie.analysis.pta.core.heap.Obj;
import pascal.taie.ir.exp.InvokeExp;
import pascal.taie.ir.exp.Var;
import pascal.taie.ir.proginfo.MethodRef;
import pascal.taie.ir.stmt.*;
import pascal.taie.language.classes.ClassHierarchy;
import pascal.taie.language.classes.JField;
import pascal.taie.language.classes.JMethod;
import pascal.taie.util.AnalysisException;
import pascal.taie.language.type.Type;

import java.awt.*;
import java.util.List;

class Solver {

    private static final Logger logger = LogManager.getLogger(Solver.class);

    private final HeapModel heapModel;

    private DefaultCallGraph callGraph;

    private PointerFlowGraph pointerFlowGraph;

    private WorkList workList;

    private StmtProcessor stmtProcessor;

    private ClassHierarchy hierarchy;

    Solver(HeapModel heapModel) {
        this.heapModel = heapModel;
    }

    /**
     * Runs pointer analysis algorithm.
     */
    void solve() {
        initialize();
        analyze();
    }

    /**
     * Initializes pointer analysis.
     */
    private void initialize() {
        workList = new WorkList();
        pointerFlowGraph = new PointerFlowGraph();
        callGraph = new DefaultCallGraph();
        stmtProcessor = new StmtProcessor();
        hierarchy = World.get().getClassHierarchy();
        // initialize main method
        JMethod main = World.get().getMainMethod();
        callGraph.addEntryMethod(main);
        addReachable(main);
    }

    /**
     * Processes new reachable method.
     */
    private void addReachable(JMethod method) {
        // TODO - finish me
        if (callGraph.addReachableMethod(method)) {
            // 处理 x = new T() in S_m
            List<Stmt> stmts = method.getIR().getStmts();
            for (Stmt stmt : stmts) {
                if (stmt instanceof New new_stmt) {
                    Obj obj = heapModel.getObj(new_stmt);
                    VarPtr var_ptr = pointerFlowGraph.getVarPtr(new_stmt.getLValue());
                    workList.addEntry(var_ptr, new PointsToSet(obj));
                } else if (stmt instanceof Copy copy_stmt) {
                    // x = y
                    Var x = copy_stmt.getLValue();
                    Var y = copy_stmt.getRValue();
                    addPFGEdge(pointerFlowGraph.getVarPtr(y), pointerFlowGraph.getVarPtr(x));
                } else if (stmt instanceof StoreField storeField && storeField.isStatic()) {
                    // 处理 T.f = y
                    JField jField = storeField.getFieldAccess().getFieldRef().resolve();
                    Var y = storeField.getRValue();
                    addPFGEdge(pointerFlowGraph.getVarPtr(y), pointerFlowGraph.getStaticField(jField));
                } else if (stmt instanceof LoadField loadField && loadField.isStatic()) {
                    // 处理 y = T.f
                    JField jField = loadField.getFieldAccess().getFieldRef().resolve();
                    Var y = loadField.getLValue();
                    addPFGEdge(pointerFlowGraph.getStaticField(jField), pointerFlowGraph.getVarPtr(y));
                } else if (stmt instanceof Invoke invoke && invoke.isStatic()) {
                    // 处理静态方法调用 , x = T.m()
                    JMethod m = resolveCallee(null, invoke);
                    CallKind callkind = CallGraphs.getCallKind(invoke);
                    assert callkind == CallKind.STATIC;
                    if (callGraph.addEdge(new Edge<>(callkind, invoke, m))) {
                        addReachable(m);
                        processHelper(m, invoke);
                    }
                }
            }
        }
    }


    /**
     * Processes statements in new reachable methods.
     */
    private class StmtProcessor implements StmtVisitor<Void> {
        // TODO - if you choose to implement addReachable()
        //  via visitor pattern, then finish me
    }

    /**
     * Adds an edge "source -> target" to the PFG.
     */
    private void addPFGEdge(Pointer source, Pointer target) {
        // TODO - finish me
        if (pointerFlowGraph.addEdge(source, target)) {
            if (!source.getPointsToSet().isEmpty()) {
                workList.addEntry(target, source.getPointsToSet());
            }
        }
    }

    /**
     * Processes work-list entries until the work-list is empty.
     */
    private void analyze() {
        // TODO - finish me
        // corresponding solve(m_entry) Part
        callGraph.entryMethods().forEach(this::addReachable);
        while (!workList.isEmpty()) {
            WorkList.Entry entry = workList.pollEntry();
            Pointer n = entry.pointer();
            PointsToSet pts = entry.pointsToSet();
            PointsToSet delta = propagate(n, pts);
            if (n instanceof VarPtr n_ptr) {
                Var x = n_ptr.getVar();
                for (Obj obj : delta) {
                    for (StoreField storeField : x.getStoreFields()) {
                        // o.f = y
                        Var y = storeField.getRValue();
                        VarPtr y_ptr = pointerFlowGraph.getVarPtr(y);
                        InstanceField instanceField = pointerFlowGraph.getInstanceField(obj, storeField.getFieldRef().resolve());
                        addPFGEdge(y_ptr, instanceField);
                    }
                    for (LoadField loadField : x.getLoadFields()) {
                        // y = o.f
                        Var y = loadField.getLValue();
                        VarPtr y_ptr = pointerFlowGraph.getVarPtr(y);
                        InstanceField instanceField = pointerFlowGraph.getInstanceField(obj, loadField.getFieldRef().resolve());
                        addPFGEdge(instanceField, y_ptr);
                    }

                    for (StoreArray storeArray : x.getStoreArrays()) {
                        // 处理Array Store x[i] = y
                        Var y = storeArray.getRValue();
                        ArrayIndex arrayIndex = pointerFlowGraph.getArrayIndex(obj);
                        addPFGEdge(pointerFlowGraph.getVarPtr(y), arrayIndex);
                    }

                    for (LoadArray loadArray : x.getLoadArrays()) {
                        // 处理Load Array y = x[i]
                        Var y = loadArray.getLValue();
                        ArrayIndex arrayIndex = pointerFlowGraph.getArrayIndex(obj);
                        addPFGEdge(arrayIndex, pointerFlowGraph.getVarPtr(y));
                    }
                    processCall(x, obj);
                }
            }

        }
    }

    /**
     * Propagates pointsToSet to pt(pointer) and its PFG successors,
     * returns the difference set of pointsToSet and pt(pointer).
     */
    private PointsToSet propagate(Pointer pointer, PointsToSet pointsToSet) {
        // TODO - finish me
        PointsToSet delta = new PointsToSet();
        PointsToSet pointer_set = pointer.getPointsToSet();
        for (Obj obj : pointsToSet) {
            if (pointer_set.contains(obj)) continue;
            pointer_set.addObject(obj);
            delta.addObject(obj);
        }
        if (!delta.isEmpty()) {
            for (Pointer s : pointerFlowGraph.getSuccsOf(pointer)) {
                workList.addEntry(s, delta);
            }
        }
        return delta;
    }

    /**
     * Processes instance calls when points-to set of the receiver variable changes.
     *
     * @param var  the variable that holds receiver objects
     * @param recv a new discovered object pointed by the variable.
     */
    private void processCall(Var var, Obj recv) {
        // TODO - finish me
        for (Invoke invoke : var.getInvokes()) {
            JMethod m = resolveCallee(recv, invoke);
            if (m.getIR().getThis() != null) {
                workList.addEntry(pointerFlowGraph.getVarPtr(m.getIR().getThis()), new PointsToSet(recv));
            }
            CallKind callKind = CallGraphs.getCallKind(invoke);
            if (callGraph.addEdge(new Edge<>(callKind, invoke, m))) {
                addReachable(m);
                processHelper(m, invoke);
            }
        }
    }

    private void processHelper(JMethod m, Invoke invoke) {
        // invoke -> m
        List<Var> args = invoke.getInvokeExp().getArgs();
        for (int i = 0; i < args.size(); i++) {
            Var param = m.getIR().getParam(i);
            Var arg = args.get(i);
            addPFGEdge(pointerFlowGraph.getVarPtr(arg), pointerFlowGraph.getVarPtr(param));
        }
        // handle return edge
        m.getIR().getReturnVars();
        if (invoke.getLValue() != null) {
            Var r = invoke.getLValue();
            for (Var ret : m.getIR().getReturnVars()) {
                addPFGEdge(pointerFlowGraph.getVarPtr(ret), pointerFlowGraph.getVarPtr(r));
            }
        }
    }


    /**
     * Resolves the callee of a call site with the receiver object.
     *
     * @param recv     the receiver object of the method call. If the callSite
     *                 is static, this parameter is ignored (i.e., can be null).
     * @param callSite the call site to be resolved.
     * @return the resolved callee.
     */
    private JMethod resolveCallee(Obj recv, Invoke callSite) {
        Type type = recv != null ? recv.getType() : null;
        return CallGraphs.resolveCallee(type, callSite);
    }

    CIPTAResult getResult() {
        return new CIPTAResult(pointerFlowGraph, callGraph);
    }
}
