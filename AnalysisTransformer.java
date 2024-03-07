import java.util.*;
import soot.*;
import soot.jimple.AnyNewExpr;
import soot.jimple.InvokeExpr;
import soot.jimple.ParameterRef;
import soot.jimple.StaticFieldRef;
import soot.jimple.ThisRef;
import soot.jimple.internal.AbstractDefinitionStmt;
import soot.jimple.internal.AbstractInstanceInvokeExpr;
import soot.jimple.internal.JArrayRef;
import soot.jimple.internal.JAssignStmt;
import soot.jimple.internal.JBreakpointStmt;
import soot.jimple.internal.JCastExpr;
import soot.jimple.internal.JDynamicInvokeExpr;
import soot.jimple.internal.JEnterMonitorStmt;
import soot.jimple.internal.JExitMonitorStmt;
import soot.jimple.internal.JGotoStmt;
import soot.jimple.internal.JIdentityStmt;
import soot.jimple.internal.JIfStmt;
import soot.jimple.internal.JInstanceFieldRef;
import soot.jimple.internal.JInterfaceInvokeExpr;
import soot.jimple.internal.JInvokeStmt;
import soot.jimple.internal.JLookupSwitchStmt;
import soot.jimple.internal.JNewArrayExpr;
import soot.jimple.internal.JNewExpr;
import soot.jimple.internal.JNewMultiArrayExpr;
import soot.jimple.internal.JNopStmt;
import soot.jimple.internal.JRetStmt;
import soot.jimple.internal.JReturnStmt;
import soot.jimple.internal.JReturnVoidStmt;
import soot.jimple.internal.JSpecialInvokeExpr;
import soot.jimple.internal.JStaticInvokeExpr;
import soot.jimple.internal.JTableSwitchStmt;
import soot.jimple.internal.JThrowStmt;
import soot.jimple.internal.JVirtualInvokeExpr;
import soot.jimple.internal.JimpleLocal;
import soot.toolkits.graph.*;
import soot.toolkits.scalar.BackwardFlowAnalysis;
import soot.toolkits.scalar.FlowSet;

public class AnalysisTransformer extends BodyTransformer {
    public static TreeMap<String, List<Integer>> result =
        new TreeMap<String, List<Integer>>();

    @Override
    protected synchronized void internalTransform(
        Body body, String phaseName, Map<String, String> options) {
        String className = body.getMethod().getDeclaringClass().getName();
        String methodName = body.getMethod().getName();
        // System.out.println("---- " + className + ":" + methodName + " ----");
        UnitGraph unitGraph = new ExceptionalUnitGraph(body);
        HashSet<Unit> workList = new HashSet<Unit>(body.getUnits());
        HashMap<Unit, PointsToGraph> inGraph =
            new HashMap<Unit, PointsToGraph>();
        HashMap<Unit, PointsToGraph> outGraph =
            new HashMap<Unit, PointsToGraph>();
        while (!workList.isEmpty()) {
            Unit u = workList.iterator().next();
            workList.remove(u);
            if (!inGraph.containsKey(u)) {
                inGraph.put(u, new PointsToGraph());
            }
            if (!outGraph.containsKey(u)) {
                outGraph.put(u, new PointsToGraph());
            }
            for (Unit pu : unitGraph.getPredsOf(u)) {
                if (outGraph.containsKey(pu))
                    inGraph.get(u).Union(outGraph.get(pu));
            }
            PointsToGraph oldOutGraph = outGraph.get(u).GetDeepCopy();
            ProcessUnit(u, inGraph, outGraph);
            if (!outGraph.get(u).EquivTo(oldOutGraph)) {
                for (Unit su : unitGraph.getSuccsOf(u)) {
                    workList.add(su);
                }
            }
        }
        PointsToGraph finalGraph = new PointsToGraph();
        for (Unit u : unitGraph.getTails()) {
            finalGraph.Union(outGraph.get(u));
        }
        result.put(
            className + ":" + methodName, finalGraph.GetEscapingObjects());
    }

    private void ProcessUnit(Unit u, HashMap<Unit, PointsToGraph> inGraph,
        HashMap<Unit, PointsToGraph> outGraph) {
        // System.out.println(u.getClass().getName() + " "
        //     + u.getJavaSourceStartLineNumber() + "      |  " + u);
        if (u instanceof JAssignStmt) {
            ProcessAssignLikeUnit(u, inGraph, outGraph);
            // handle escaping objects in invoke expressions
            Value rightOp = ((JAssignStmt) u).getRightOp();
            if (rightOp instanceof InvokeExpr) {
                InvokeExpr invokeExpr = (InvokeExpr) rightOp;
                if (!invokeExpr.getMethodRef()
                         .isConstructor()) { // Assuming constructor doesn't
                    // escape anything
                    // staticInvoke + dynamicInvoke +
                    // other instanceInvokes
                    PointsToGraph currOutGraph = outGraph.get(u);
                    HashSet<String> escapingObjs = new HashSet<>();
                    for (Value value : invokeExpr.getArgs()) {
                        escapingObjs.addAll(
                            currOutGraph.GetAllPointsToNodes(value, u, false));
                    }
                    if (invokeExpr instanceof JInterfaceInvokeExpr
                        || invokeExpr instanceof JSpecialInvokeExpr
                        || invokeExpr instanceof JVirtualInvokeExpr) {
                        AbstractInstanceInvokeExpr instanceInvokeExpr =
                            (AbstractInstanceInvokeExpr) invokeExpr;
                        Value base = instanceInvokeExpr.getBase();
                        escapingObjs.addAll(
                            currOutGraph.GetAllPointsToNodes(base, u, false));
                    }
                    currOutGraph.MarkAsEscaping(escapingObjs);
                    outGraph.put(u, currOutGraph);
                }
            }
            return;
        }

        else if (u instanceof JIdentityStmt) {
            // is semantically like the JAssignStmt and handles
            // assignments of IdentityRef's to make implicit assignments
            // explicit into the StmtGraph.
            ProcessAssignLikeUnit(u, inGraph, outGraph);
            return;
        }

        else if (u instanceof JReturnStmt) {
            JReturnStmt returnStmt = (JReturnStmt) u;
            Value op = returnStmt.getOp();
            PointsToGraph currInGraph = inGraph.get(u);
            PointsToGraph currOutGraph = null;
            HashSet<String> nodes =
                currInGraph.GetAllPointsToNodes(op, u, false);
            currOutGraph = currInGraph.GetDeepCopy();
            currOutGraph.MarkAsEscaping(nodes);
            inGraph.put(u, currInGraph);
            outGraph.put(u, currOutGraph);
            return;
        } else if (u instanceof JGotoStmt) {
        } else if (u instanceof JReturnVoidStmt) {
        } else if (u instanceof JTableSwitchStmt) {
        } else if (u instanceof JInvokeStmt) {
            JInvokeStmt jInvokeStmt = (JInvokeStmt) u;
            InvokeExpr invokeExpr = jInvokeStmt.getInvokeExpr();
            if (!invokeExpr.getMethodRef()
                     .isConstructor()) { // Assuming constructor doesn't
                                         // escape anything
                // staticInvoke + dynamicInvoke + other instanceInvokes
                PointsToGraph currInGraph = inGraph.get(u);
                HashSet<String> escapingObjs = new HashSet<>();
                for (Value value : invokeExpr.getArgs()) {
                    escapingObjs.addAll(
                        currInGraph.GetAllPointsToNodes(value, u, false));
                }
                if (invokeExpr instanceof JInterfaceInvokeExpr
                    || invokeExpr instanceof JSpecialInvokeExpr
                    || invokeExpr instanceof JVirtualInvokeExpr) {
                    AbstractInstanceInvokeExpr instanceInvokeExpr =
                        (AbstractInstanceInvokeExpr) invokeExpr;
                    Value base = instanceInvokeExpr.getBase();
                    escapingObjs.addAll(
                        currInGraph.GetAllPointsToNodes(base, u, false));
                }
                PointsToGraph currOutGraph = currInGraph.GetDeepCopy();
                currOutGraph.MarkAsEscaping(escapingObjs);
                inGraph.put(u, currInGraph);
                outGraph.put(u, currOutGraph);
                return;
            }
        } else if (u instanceof JNopStmt) {
        } else if (u instanceof JBreakpointStmt) { // not relevant for
                                                   // static analysis
        } else if (u instanceof JLookupSwitchStmt) { // switch statement
        } else if (u instanceof JIfStmt) {
            // Handle JIfStmt
        }
        outGraph.put(u, inGraph.get(u).GetDeepCopy());
    }

    private void ProcessAssignLikeUnit(Unit u,
        HashMap<Unit, PointsToGraph> inGraph,
        HashMap<Unit, PointsToGraph>
            outGraph) { // for JAssignStmt and JIdentityStmt
        PointsToGraph currInGraph = inGraph.get(u);
        PointsToGraph currOutGraph = null;
        AbstractDefinitionStmt stmt = (AbstractDefinitionStmt) u;
        Value leftOp = stmt.getLeftOp();
        Value rightOp = stmt.getRightOp();
        HashSet<String> lNodes =
            currInGraph.GetAllPointsToNodes(leftOp, u, true);
        HashSet<String> rNodes =
            currInGraph.GetAllPointsToNodes(rightOp, u, false);
        String edge = PointsToGraph.emptyEdge;
        Boolean isStrongUpdate = false;
        if (leftOp instanceof JInstanceFieldRef) {
            JInstanceFieldRef jInstanceFieldRef = (JInstanceFieldRef) leftOp;
            edge = jInstanceFieldRef.getField().toString();
        } else if (leftOp instanceof JArrayRef) {
            edge = "[]";
            // TODO: check, nothing else can add a non-empty edge
        }
        if (!(leftOp instanceof JInstanceFieldRef)
            && !(leftOp instanceof JArrayRef)
            && !(leftOp instanceof StaticFieldRef)) {
            isStrongUpdate = true;
            // TODO: check
        }
        currOutGraph = currInGraph.GetDeepCopy();
        currOutGraph.Connect(lNodes, rNodes, edge, isStrongUpdate);
        // System.out.println(lNodes + " " + rNodes);
        inGraph.put(u, currInGraph);
        outGraph.put(u, currOutGraph);
        // System.out.println(currOutGraph.graph);
    }
}

class PointsToGraph {
    static String emptyEdge = "-";
    HashMap<String, HashMap<String, HashSet<String>>> graph;
    HashSet<String> escapingObjects;
    HashSet<String> dummyNodes;
    HashSet<String> localNodes;
    HashSet<String> heapNodes;
    HashSet<String> globalNodes;
    HashSet<String> allNodes;
    // allNodes = dummyNodes U localNodes U heapNodes U globalNodes
    public PointsToGraph() {
        graph = new HashMap<String, HashMap<String, HashSet<String>>>();
        escapingObjects = new HashSet<String>();
        dummyNodes = new HashSet<String>();
        localNodes = new HashSet<String>();
        heapNodes = new HashSet<String>();
        globalNodes = new HashSet<String>();
        allNodes = new HashSet<String>();
    }

    public void Union(PointsToGraph ptg) {
        for (String key : ptg.graph.keySet()) {
            if (!graph.containsKey(key)) {
                graph.put(key, new HashMap<String, HashSet<String>>());
            }
            for (String key2 : ptg.graph.get(key).keySet()) {
                if (!graph.get(key).containsKey(key2)) {
                    graph.get(key).put(key2, new HashSet<String>());
                }
                graph.get(key).get(key2).addAll(ptg.graph.get(key).get(key2));
            }
        }
        escapingObjects.addAll(ptg.escapingObjects);
        dummyNodes.addAll(ptg.dummyNodes);
        localNodes.addAll(ptg.localNodes);
        heapNodes.addAll(ptg.heapNodes);
        globalNodes.addAll(ptg.globalNodes);
        allNodes.addAll(ptg.allNodes);
    }

    public PointsToGraph GetDeepCopy() {
        PointsToGraph ptg = new PointsToGraph();
        for (String key : graph.keySet()) {
            ptg.graph.put(key, new HashMap<String, HashSet<String>>());
            for (String key2 : graph.get(key).keySet()) {
                ptg.graph.get(key).put(key2, new HashSet<String>());
                ptg.graph.get(key).get(key2).addAll(graph.get(key).get(key2));
            }
        }
        ptg.escapingObjects.addAll(escapingObjects);
        ptg.dummyNodes.addAll(dummyNodes);
        ptg.localNodes.addAll(localNodes);
        ptg.heapNodes.addAll(heapNodes);
        ptg.globalNodes.addAll(globalNodes);
        ptg.allNodes.addAll(allNodes);
        return ptg;
    }

    public Boolean EquivTo(PointsToGraph ptg) {
        // TODO: check
        for (String key : graph.keySet()) {
            if (ptg.graph.containsKey(key)) {
                for (String key2 : graph.get(key).keySet()) {
                    if (ptg.graph.get(key).containsKey(key2)) {
                        if (!graph.get(key).get(key2).equals(
                                ptg.graph.get(key).get(key2))) {
                            return false;
                        }
                    } else {
                        return false;
                    }
                }
            } else {
                return false;
            }
        }
        if (!escapingObjects.equals(ptg.escapingObjects))
            return false;
        if (!dummyNodes.equals(ptg.dummyNodes))
            return false;
        if (!localNodes.equals(ptg.localNodes))
            return false;
        if (!heapNodes.equals(ptg.heapNodes))
            return false;
        if (!globalNodes.equals(ptg.globalNodes))
            return false;
        if (!allNodes.equals(ptg.allNodes))
            return false;
        return true;
    }

    public HashSet<String> GetAllPointsToNodes(
        Value value, Unit u, Boolean isLeftOp) {
        HashSet<String> nodes = new HashSet<String>();
        if (value instanceof JArrayRef) {
            JArrayRef jArrayRef = (JArrayRef) value;
            Value base = jArrayRef.getBase();
            String baseNode = base.toString();
            if (isLeftOp) {
                if (graph.containsKey(baseNode)) {
                    if (graph.get(baseNode).containsKey(emptyEdge)) {
                        nodes.addAll(graph.get(baseNode).get(emptyEdge));
                    }
                }
            } else {
                if (graph.containsKey(baseNode)) {
                    if (graph.get(baseNode).containsKey(emptyEdge)) {
                        for (String lev1Node :
                            graph.get(baseNode).get(emptyEdge)) {
                            if (graph.get(lev1Node).containsKey("[]")) {
                                for (String refNode :
                                    graph.get(lev1Node).get("[]")) {
                                    nodes.add(refNode);
                                }
                            }
                        }
                    }
                }
            }
        } else if (value instanceof JCastExpr) {
            JCastExpr jCastExpr = (JCastExpr) value;
            return GetAllPointsToNodes(jCastExpr.getOp(), u, false);
        } else if (value instanceof JimpleLocal) {
            String localNode = value.toString();
            if (!graph.containsKey(localNode)) {
                AddLocalNode(localNode);
            }
            if (isLeftOp)
                nodes.add(localNode);
            else {
                if (graph.get(localNode).containsKey(emptyEdge)) {
                    nodes.addAll(graph.get(localNode).get(emptyEdge));
                }
            }
        } else if (value instanceof JInstanceFieldRef) {
            JInstanceFieldRef jInstanceFieldRef = (JInstanceFieldRef) value;
            String baseStr = jInstanceFieldRef.getBase().toString();
            String fieldStr = jInstanceFieldRef.getField().toString();
            if (graph.containsKey(baseStr)) {
                if (graph.get(baseStr).containsKey(emptyEdge)) {
                    if (isLeftOp)
                        nodes.addAll(graph.get(baseStr).get(emptyEdge));
                    else {
                        for (String lev1Node :
                            graph.get(baseStr).get(emptyEdge)) {
                            if (IsDummy(lev1Node)) {
                                String dummyNode = lev1Node;
                                String commonField = "common_field";
                                if (!graph.get(lev1Node).containsKey(
                                        "common_field")) {
                                    ConnectTwoNodes(dummyNode, dummyNode,
                                        commonField, false);
                                }
                                for (String node :
                                    graph.get(lev1Node).get(commonField)) {
                                    nodes.add(node);
                                }
                                if (graph.get(lev1Node).containsKey(fieldStr)) {
                                    for (String node :
                                        graph.get(lev1Node).get(fieldStr)) {
                                        nodes.add(node);
                                    }
                                }
                            }

                            if (!graph.get(lev1Node).containsKey(fieldStr))
                                continue;
                            for (String node :
                                graph.get(lev1Node).get(fieldStr)) {
                                nodes.add(node);
                            }
                        }
                    }
                }
            }
        } else if (value instanceof JNewExpr
            || value instanceof JNewArrayExpr) { // array new()s are also to be
                                                 // handled the same way
            String objectNode =
                Integer.toString(u.getJavaSourceStartLineNumber());
            AddHeapNode(objectNode);
            nodes.add(objectNode);
        } else if (value instanceof JNewMultiArrayExpr) {
        } else if (value instanceof NullType) {
        } else if (value instanceof ParameterRef) {
            // TODO: check, maybe create another dummy node? can it be on
            // rhs?
            if (!(value.getType() instanceof PrimType)) {
                String dummyNode =
                    "dummy_" + value.toString(); // param is pointing to
                                                 // this dummy node
                AddDummyNode(dummyNode);
                nodes.add(dummyNode);
            }
        } else if (value instanceof StaticFieldRef) {
            if (!(value.getType() instanceof PrimType)) {
                StaticFieldRef staticFieldRef = (StaticFieldRef) value;
                String staticNode = staticFieldRef.getField().toString();
                if (!globalNodes.contains(staticNode)) {
                    AddGlobalNode(staticNode);
                }
                if (isLeftOp) {
                    nodes.add(staticNode);
                } else {
                    if (graph.get(staticNode).containsKey(emptyEdge)) {
                        nodes.addAll(graph.get(staticNode).get(emptyEdge));
                    }
                }
            }

        } else if (value instanceof ThisRef) {
            String thisNode = value.toString();
            if (!globalNodes.contains(thisNode)) {
                AddGlobalNode(thisNode);
            }
            if (isLeftOp) {
                nodes.add(thisNode);
            } else {
                if (graph.get(thisNode).containsKey(emptyEdge)) {
                    nodes.addAll(graph.get(thisNode).get(emptyEdge));
                }
            }
        } else if (value instanceof JInterfaceInvokeExpr
            || value instanceof JSpecialInvokeExpr
            || value instanceof JStaticInvokeExpr
            || value instanceof JVirtualInvokeExpr) {
            // Note that escaping objects are marked in the ProcessUnit
            // itself
            String dummyNode = "dummy_#" + u.getJavaSourceStartLineNumber();
            // System.out.println(dummyNode);
            if (!dummyNodes.contains(dummyNode))
                AddDummyNode(dummyNode);
            nodes.add(dummyNode);
        } else if (value instanceof JDynamicInvokeExpr) {
        }
        return nodes;
    }

    public void Connect(HashSet<String> lNodes, HashSet<String> rNodes,
        String edge, Boolean isStrongUpdate) {
        for (String lNode : lNodes) {
            if (!graph.containsKey(lNode))
                throw new RuntimeException(
                    "lNode not in graph: " + graph + " " + lNode);
        }
        for (String rNode : rNodes) {
            if (!graph.containsKey(rNode))
                throw new RuntimeException(
                    "rNode not in graph: " + graph + " " + rNode);
        }
        // connect
        if (isStrongUpdate) { // JInstanceFieldRef or JArrayRef
            for (String lNode : lNodes) {
                if (!graph.get(lNode).containsKey(edge))
                    graph.get(lNode).put(edge, new HashSet<String>());
                graph.get(lNode).get(edge).clear();
                if (!rNodes.isEmpty())
                    graph.get(lNode).get(edge).addAll(rNodes);
            }
        } else {
            for (String lNode : lNodes) {
                if (!graph.get(lNode).containsKey(edge))
                    graph.get(lNode).put(edge, new HashSet<String>());
                if (!rNodes.isEmpty())
                    graph.get(lNode).get(edge).addAll(rNodes);
            }
        }
    }

    public void ConnectTwoNodes(
        String lNode, String rNode, String edge, Boolean isStrongUpdate) {
        HashSet<String> rNodes = new HashSet<String>();
        rNodes.add(rNode);
        HashSet<String> lNodes = new HashSet<String>();
        lNodes.add(lNode);
        Connect(lNodes, rNodes, edge, isStrongUpdate);
    }

    public Boolean IsDummy(String node) {
        return dummyNodes.contains(node);
    }

    public Boolean IsHeapNode(String node) {
        return heapNodes.contains(node);
    }

    public void MarkAsEscaping(HashSet<String> nodes) {
        escapingObjects.addAll(nodes);
    }

    private void AddLocalNode(String node) {
        graph.put(node, new HashMap<String, HashSet<String>>());
        localNodes.add(node);
        allNodes.add(node);
    }

    private void AddHeapNode(String node) {
        graph.put(node, new HashMap<String, HashSet<String>>());
        heapNodes.add(node);
        allNodes.add(node);
    }

    private void AddGlobalNode(String node) { // static & this nodes
        graph.put(node, new HashMap<String, HashSet<String>>());
        globalNodes.add(node);
        escapingObjects.add(node);
        allNodes.add(node);

        String dummyNode = "dummy_" + node;
        AddDummyNode(dummyNode);

        ConnectTwoNodes(node, dummyNode, emptyEdge, true);
    }

    private void AddDummyNode(String node) {
        graph.put(node, new HashMap<String, HashSet<String>>());
        dummyNodes.add(node);
        allNodes.add(node);
        escapingObjects.add(node);
    }

    public List<Integer> GetEscapingObjects() {
        HashSet<String> allEscapingObjects = new HashSet<String>();
        for (String node : escapingObjects) {
            AddReachableNodes(node, allEscapingObjects);
        }
        List<Integer> lineNumbers = new ArrayList<Integer>();
        for (String node : allEscapingObjects) {
            if (IsHeapNode(node)) {
                lineNumbers.add(Integer.parseInt(node));
            }
        }
        Collections.sort(lineNumbers);
        return lineNumbers;
    }

    public void AddReachableNodes(String node, HashSet<String> reachableNodes) {
        reachableNodes.add(node);
        for (String edge : graph.get(node).keySet()) {
            for (String nextNode : graph.get(node).get(edge)) {
                if (!reachableNodes.contains(nextNode)) {
                    AddReachableNodes(nextNode, reachableNodes);
                }
            }
        }
    }
}
