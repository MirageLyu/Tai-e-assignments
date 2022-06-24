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
import pascal.taie.ir.stmt.Stmt;
import pascal.taie.language.classes.ClassHierarchy;
import pascal.taie.language.classes.JClass;
import pascal.taie.language.classes.JMethod;
import pascal.taie.language.classes.Subsignature;

import java.util.*;

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
        return callGraph;
    }

    /**
     * Resolves call targets (callees) of a call site via CHA.
     */
    private Set<JMethod> resolve(Invoke callSite) {
        Set<JMethod> set = new HashSet<>();

        if (callSite.isStatic()) {
            set.add(callSite.getContainer());
        }
        else if (callSite.isSpecial()) {
            JClass cm = callSite.getContainer().getDeclaringClass();
            JMethod m = dispatch(cm, callSite.getMethodRef().getSubsignature());
            if (m != null) {
                set.add(m);
            }
        }
        else if (callSite.isVirtual()) {
            JClass receiver = callSite.getContainer().getDeclaringClass();
            Queue<JClass> classQueue = new ArrayDeque<>();
            classQueue.add(receiver);
            while (!classQueue.isEmpty()) {
                JClass jClass = classQueue.poll();
                JMethod m = dispatch(jClass, callSite.getMethodRef().getSubsignature());
                if (m != null) {
                    set.add(m);
                }
                classQueue.addAll(hierarchy.getDirectImplementorsOf(jClass));
                classQueue.addAll(hierarchy.getDirectSubclassesOf(jClass));
                classQueue.addAll(hierarchy.getDirectSubinterfacesOf(jClass));
            }
        }
        
        return set;
    }

    /**
     * Looks up the target method based on given class and method subsignature.
     *
     * @return the dispatched target method, or null if no satisfying method
     * can be found.
     */
    private JMethod dispatch(JClass jclass, Subsignature subsignature) {
        if (jclass != null && !jclass.isInterface()) {
            JMethod jm = jclass.getDeclaredMethod(subsignature);
            if (jm != null && !jm.isAbstract()) {
                return jm;
            }
            return dispatch(jclass.getSuperClass(), subsignature);
        }
        return null;
    }
}
