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

package pascal.taie.analysis.pta.cs;

import org.apache.logging.log4j.LogManager;
import org.apache.logging.log4j.Logger;
import pascal.taie.World;
import pascal.taie.analysis.graph.callgraph.CallGraphs;
import pascal.taie.analysis.graph.callgraph.CallKind;
import pascal.taie.analysis.graph.callgraph.Edge;
import pascal.taie.analysis.pta.PointerAnalysisResult;
import pascal.taie.analysis.pta.PointerAnalysisResultImpl;
import pascal.taie.analysis.pta.core.cs.CSCallGraph;
import pascal.taie.analysis.pta.core.cs.context.Context;
import pascal.taie.analysis.pta.core.cs.element.ArrayIndex;
import pascal.taie.analysis.pta.core.cs.element.CSCallSite;
import pascal.taie.analysis.pta.core.cs.element.CSManager;
import pascal.taie.analysis.pta.core.cs.element.CSMethod;
import pascal.taie.analysis.pta.core.cs.element.CSObj;
import pascal.taie.analysis.pta.core.cs.element.CSVar;
import pascal.taie.analysis.pta.core.cs.element.InstanceField;
import pascal.taie.analysis.pta.core.cs.element.MapBasedCSManager;
import pascal.taie.analysis.pta.core.cs.element.Pointer;
import pascal.taie.analysis.pta.core.cs.element.StaticField;
import pascal.taie.analysis.pta.core.cs.selector.ContextSelector;
import pascal.taie.analysis.pta.core.heap.HeapModel;
import pascal.taie.analysis.pta.core.heap.Obj;
import pascal.taie.analysis.pta.pts.PointsToSet;
import pascal.taie.analysis.pta.pts.PointsToSetFactory;
import pascal.taie.config.AnalysisOptions;
import pascal.taie.ir.exp.InvokeExp;
import pascal.taie.ir.exp.Var;
import pascal.taie.ir.stmt.*;
import pascal.taie.language.classes.JField;
import pascal.taie.language.classes.JMethod;
import pascal.taie.language.type.Type;

import java.util.List;

class Solver {

    private static final Logger logger = LogManager.getLogger(Solver.class);

    private final AnalysisOptions options;

    private final HeapModel heapModel;

    private final ContextSelector contextSelector;

    private CSManager csManager;

    private CSCallGraph callGraph;

    private PointerFlowGraph pointerFlowGraph;

    private WorkList workList;

    private PointerAnalysisResult result;

    Solver(AnalysisOptions options, HeapModel heapModel,
           ContextSelector contextSelector) {
        this.options = options;
        this.heapModel = heapModel;
        this.contextSelector = contextSelector;
    }

    void solve() {
        initialize();
        analyze();
    }

    private void initialize() {
        csManager = new MapBasedCSManager();
        callGraph = new CSCallGraph(csManager);
        pointerFlowGraph = new PointerFlowGraph();
        workList = new WorkList();
        // process program entry, i.e., main method
        Context defContext = contextSelector.getEmptyContext();
        JMethod main = World.get().getMainMethod();
        CSMethod csMethod = csManager.getCSMethod(defContext, main);
        callGraph.addEntryMethod(csMethod);
        addReachable(csMethod);
    }

    /**
     * Processes new reachable context-sensitive method.
     */
    private void addReachable(CSMethod csMethod) {
        // TODO - finish me
        Context context = csMethod.getContext();
        if ((callGraph.addReachableMethod(csMethod))) {
            List<Stmt> stmts = csMethod.getMethod().getIR().getStmts();
            for (Stmt stmt : stmts) {
                if (stmt instanceof New new_stmt) {
                    // 处理new语句
                    Obj obj = heapModel.getObj(new_stmt);
                    CSVar csVar = csManager.getCSVar(context, new_stmt.getLValue());
                    CSObj csobj = csManager.getCSObj(contextSelector.selectHeapContext(csMethod, obj), obj);
                    workList.addEntry(csVar, PointsToSetFactory.make(csobj));
                } else if (stmt instanceof Copy copy_stmt) {
                    // 处理 c:x = c:y
                    CSVar csVar_x = csManager.getCSVar(context, copy_stmt.getLValue());
                    CSVar csVar_y = csManager.getCSVar(context, copy_stmt.getRValue());
                    addPFGEdge(csVar_y, csVar_x);
                } else if (stmt instanceof StoreField storeField && storeField.isStatic()) {
                    // T.f = c:y
                    JField jField = storeField.getFieldAccess().getFieldRef().resolve();
                    Var y = storeField.getRValue();
                    addPFGEdge(csManager.getCSVar(context, y), csManager.getStaticField(jField));
                } else if (stmt instanceof LoadField loadField && loadField.isStatic()) {
                    // 处理 c:y = T.f
                    JField jField = loadField.getFieldAccess().getFieldRef().resolve();
                    Var y = loadField.getLValue();
                    addPFGEdge(csManager.getStaticField(jField), csManager.getCSVar(context, y));
                } else if (stmt instanceof Invoke invoke && invoke.isStatic()) {
                    // 处理静态方法调用，c:x = T.m()
                    JMethod m = resolveCallee(null, invoke);
                    CallKind callKind = CallGraphs.getCallKind(invoke);
                    assert callKind == CallKind.STATIC;
                    CSCallSite csCallSite = csManager.getCSCallSite(context, invoke);
                    Context context_t = contextSelector.selectContext(csCallSite, m);
                    if (callGraph.addEdge(new Edge<>(callKind, csCallSite, csManager.getCSMethod(context_t, m)))) {
                        addReachable(csManager.getCSMethod(context_t, m));
                        processHelper(context, context_t, m, invoke);
                    }
                }
            }
        }
    }

    private void processHelper(Context prev, Context cur, JMethod m, Invoke invoke) {
        // invoke -> m
        List<Var> args = invoke.getInvokeExp().getArgs();
        for (int i = 0; i < args.size(); i++) {
            Var param = m.getIR().getParam(i);
            Var arg = args.get(i);
            addPFGEdge(csManager.getCSVar(prev, arg), csManager.getCSVar(cur, param));
        }
        // handle return edge
        m.getIR().getReturnVars();
        if (invoke.getLValue() != null) {
            Var r = invoke.getLValue();
            for (Var ret : m.getIR().getReturnVars()) {
                addPFGEdge(csManager.getCSVar(cur, ret), csManager.getCSVar(prev, r));
            }
        }
    }

    /**
     * Processes the statements in context-sensitive new reachable methods.
     */
    private class StmtProcessor implements StmtVisitor<Void> {

        private final CSMethod csMethod;

        private final Context context;

        private StmtProcessor(CSMethod csMethod) {
            this.csMethod = csMethod;
            this.context = csMethod.getContext();
        }

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
        callGraph.entryMethods().forEach(this::addReachable);
        while (!workList.isEmpty()) {
            WorkList.Entry entry = workList.pollEntry();
            Pointer n = entry.pointer();
            PointsToSet pts = entry.pointsToSet();
            PointsToSet delta = propagate(n, pts);
            if (delta.isEmpty()) continue;
            if (n instanceof CSVar n_ptr) {
                Var x = n_ptr.getVar();
                Context context = n_ptr.getContext();
                for (CSObj obj : delta) {
                    for (StoreField storeField : x.getStoreFields()) {
                        // c':o.f = c:y
                        Var y = storeField.getRValue();
                        CSVar y_ptr = csManager.getCSVar(context, y);
                        InstanceField instanceField = csManager.getInstanceField(obj, storeField.getFieldRef().resolve());
                        addPFGEdge(y_ptr, instanceField);
                    }
                    for (LoadField loadField : x.getLoadFields()) {
                        // c:y = c':o.f
                        Var y = loadField.getLValue();
                        CSVar y_ptr = csManager.getCSVar(context, y);
                        InstanceField instanceField = csManager.getInstanceField(obj, loadField.getFieldRef().resolve());
                        addPFGEdge(instanceField, y_ptr);
                    }

                    for (StoreArray storeArray : x.getStoreArrays()) {
                        // 处理Array Store c':x[i] = c:y
                        Var y = storeArray.getRValue();
                        CSVar y_ptr = csManager.getCSVar(context, y);
                        ArrayIndex arrayIndex = csManager.getArrayIndex(obj);
                        addPFGEdge(y_ptr, arrayIndex);
                    }

                    for (LoadArray loadArray : x.getLoadArrays()) {
                        // 处理Load Array c:y = c':x[i]
                        Var y = loadArray.getLValue();
                        CSVar y_ptr = csManager.getCSVar(context, y);
                        ArrayIndex arrayIndex = csManager.getArrayIndex(obj);
                        addPFGEdge(arrayIndex, y_ptr);
                    }
                    processCall(n_ptr, obj);
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
        PointsToSet delta = PointsToSetFactory.make();
        PointsToSet pointer_set = pointer.getPointsToSet();
        for (CSObj obj : pointsToSet) {
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
     * @param recv    the receiver variable
     * @param recvObj set of new discovered objects pointed by the variable.
     */
    private void processCall(CSVar recv, CSObj recvObj) {
        // TODO - finish me
        // c:x : c':o_i
        Context context = recv.getContext();
        for (Invoke invoke : recv.getVar().getInvokes()) {
            JMethod m = resolveCallee(recvObj, invoke);
            CSCallSite csCallSite = csManager.getCSCallSite(context, invoke);
            // resolve callee context
            Context context_t = contextSelector.selectContext(csCallSite, recvObj, m);
            CallKind callKind = CallGraphs.getCallKind(invoke);
            CSMethod csMethod = csManager.getCSMethod(context_t, m);
            if (m.getIR().getThis() != null) {
                // i.e instance method call
                workList.addEntry(csManager.getCSVar(context_t, m.getIR().getThis()), PointsToSetFactory.make(recvObj));
            }
            if (callGraph.addEdge(new Edge<>(callKind, csCallSite, csMethod))) {
                addReachable(csMethod);
                processHelper(context, context_t, m, invoke);
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
    private JMethod resolveCallee(CSObj recv, Invoke callSite) {
        Type type = recv != null ? recv.getObject().getType() : null;
        return CallGraphs.resolveCallee(type, callSite);
    }

    PointerAnalysisResult getResult() {
        if (result == null) {
            result = new PointerAnalysisResultImpl(csManager, callGraph);
        }
        return result;
    }
}
