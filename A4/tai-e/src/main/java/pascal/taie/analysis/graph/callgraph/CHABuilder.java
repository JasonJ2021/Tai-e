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

package pascal.taie.analysis.graph.callgraph;

import pascal.taie.World;
import pascal.taie.ir.proginfo.MethodRef;
import pascal.taie.ir.stmt.Invoke;
import pascal.taie.language.classes.ClassHierarchy;
import pascal.taie.language.classes.JClass;
import pascal.taie.language.classes.JMethod;
import pascal.taie.language.classes.Subsignature;

import java.util.*;
import java.util.jar.JarEntry;
import java.util.stream.Stream;

/**
 * Implementation of the CHA algorithm.
 */
class CHABuilder implements CGBuilder<Invoke, JMethod> {

    private ClassHierarchy hierarchy;

    @Override
    public CallGraph<Invoke, JMethod> build() {
        hierarchy = World.get().getClassHierarchy();
        return buildCallGraph(World.get().getMainMethod());
    }

    private CallGraph<Invoke, JMethod> buildCallGraph(JMethod entry) {
        DefaultCallGraph callGraph = new DefaultCallGraph();
        callGraph.addEntryMethod(entry);
        // TODO - finish me
        Deque<JMethod> WL = new ArrayDeque<>();
        WL.addLast(entry);
        while (!WL.isEmpty()) {
            JMethod m = WL.removeFirst();
            if (callGraph.addReachableMethod(m)) {
                Stream<Invoke> invokeStream = callGraph.callSitesIn(m);
                invokeStream.forEach((cs) -> {
                    Set<JMethod> T = resolve(cs);
                    for (JMethod target : T) {
                        CallKind callkind = CallGraphs.getCallKind(cs);
                        callGraph.addEdge(new Edge<>(callkind, cs, target));
                        WL.addLast(target);
                    }
                });
            }
        }
        return callGraph;
    }

    /**
     * Resolves call targets (callees) of a call site via CHA.
     */
    private Set<JMethod> resolve(Invoke callSite) {
        // TODO - finish me
        Set<JMethod> T = new HashSet<>();
        Subsignature m = callSite.getMethodRef().getSubsignature();
        JClass jclass = callSite.getMethodRef().getDeclaringClass();
        CallKind callKind = CallGraphs.getCallKind(callSite);
        if (callKind == CallKind.STATIC) {
            // invokestatic
            JMethod target_method = jclass.getDeclaredMethod(m);
            if (target_method != null) T.add(target_method);
        } else if (callKind == CallKind.SPECIAL) {
            JMethod target_method = dispatch(jclass, m);
            if (target_method != null) T.add(target_method);
        } else if (callKind == CallKind.VIRTUAL || callKind == CallKind.INTERFACE) {
            Deque<JClass> deque = new ArrayDeque<>();
            deque.addLast(jclass);
            while (!deque.isEmpty()) {
                JClass c_t = deque.removeFirst();
                JMethod dispatch_method = dispatch(c_t, m);
                if (dispatch_method != null) T.add(dispatch_method);
                if (c_t.isInterface()) {
                    deque.addAll(hierarchy.getDirectImplementorsOf(c_t));
                    deque.addAll(hierarchy.getDirectSubinterfacesOf(c_t));
                } else {
                    deque.addAll(hierarchy.getDirectSubclassesOf(c_t));
                }
            }
        }
        return T;
    }

    /**
     * Looks up the target method based on given class and method subsignature.
     *
     * @return the dispatched target method, or null if no satisfying method
     * can be found.
     */
    private JMethod dispatch(JClass jclass, Subsignature subsignature) {
        // TODO - finish me
        if (jclass == null) return null;
        JMethod target = jclass.getDeclaredMethod(subsignature);
        if (target != null && !target.isAbstract()) return target;
        return dispatch(jclass.getSuperClass(), subsignature);
    }
}
