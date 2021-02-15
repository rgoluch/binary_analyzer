package com.kcsl.x86.isomorphism;

import com.ensoftcorp.atlas.core.db.graph.Edge;
import com.ensoftcorp.atlas.core.db.graph.Graph;
import com.ensoftcorp.atlas.core.db.graph.Node;
import com.ensoftcorp.atlas.core.db.set.AtlasSet;
import com.ensoftcorp.atlas.core.query.Q;
import com.ensoftcorp.atlas.core.xcsg.XCSG;

import static com.kcsl.x86.static_function_transform.StaticFunctionChecking.*;
import static com.kcsl.x86.switch_transform.SwitchStatementChecking.*;

import java.util.ArrayList;
import java.util.HashMap;
import java.util.LinkedList;
import java.util.Map;
import java.util.Queue;
import java.util.Stack;

import static com.kcsl.x86.subgraphs.SubGraphGenerator.*;

public class IsomorphismChecking {
	
	public static Q createSrcGraph(String functionName) {
		
		Q staticSrcGraph = staticTransform(functionName);
		Q switchSrcGraph = switchTransform(functionName, staticSrcGraph);
		String name = switchSrcGraph.containers().nodes(XCSG.Function).eval().nodes().one().getAttr(XCSG.name).toString();
		Q scSrcGraph = singleSrcReturn(switchSrcGraph, name, 1);
		Q srcSubGraph = findSrcSubGraph(scSrcGraph);
		
		return srcSubGraph;
	}
	
	public static void isomorphismChecker(String functionName) {
		String srcName = functionName.substring(4);
		Q srcGraph = createSrcGraph(srcName);
		Q binGraph = findSubGraph(functionName);
		
		Map<Node, isoNode> srcIsoNodes = new HashMap<Node, isoNode>();
		Map<Node, isoNode> binIsoNodes = new HashMap<Node, isoNode>();
		
		ArrayList<isoNode> srcCreatedIso = new ArrayList<isoNode>();
		ArrayList<isoNode> binCreatedIso = new ArrayList<isoNode>();

		int srcLabel = 1; 
		
		AtlasSet<Node> srcLoopHeaders = srcGraph.eval().nodes().tagged(XCSG.ControlFlowLoopCondition);
		AtlasSet<Node> binLoopHeaders = binGraph.eval().nodes().tagged(XCSG.ControlFlowLoopCondition);
		
		//Sanity check that we have the same number of loops
		if (srcLoopHeaders.size() != binLoopHeaders.size()) {
			System.err.println("Loop header count mismatch");
			return;
		}
//		System.out.println("src: "+srcGraph.eval().nodes().tagged("src_node").size());
//		System.out.println("bin: "+binGraph.eval().nodes().tagged("bin_node").size());
		if (srcGraph.eval().nodes().tagged("src_node").size() != binGraph.eval().nodes().tagged("bin_node").size()) {
			System.err.println("Node count mismatch");
			return;
		}
		
		for (Node l : srcLoopHeaders) {
			isoNode i = new isoNode(l, srcLabel);
			srcLabel +=1;
			srcIsoNodes.put(l, i);			
		}
		
		int binLabel = 1;
		//Handle binary graph 
		for (Node l : binLoopHeaders) {
			isoNode i = new isoNode(l, binLabel);
			binLabel +=1;
			binIsoNodes.put(l, i);			
		}
		
		Node srcRoot = srcGraph.eval().roots().getFirst();
		AtlasSet<Edge> rootOut = srcRoot.out().tagged("src_induced_edge");
		isoNode r = new isoNode(srcRoot, srcLabel);
		r.depth.add(0);
		
		srcIsoNodes.put(srcRoot, r);
		srcCreatedIso.add(r);
		srcLabel +=1;
		
		AtlasSet<Node> srcNodes = srcGraph.eval().nodes().tagged("src_node");
		Queue<Node> srcQ = new LinkedList<Node>();
		Node falseNode = null;
		for(Edge e : rootOut) {
			if (e.hasAttr(XCSG.conditionValue)) {
				if (e.getAttr(XCSG.conditionValue).toString().contains("true")) {
					srcQ.add(e.to());
				}else {
					falseNode = e.to();
				}
			}
		}
		srcQ.add(falseNode);
		
		while(srcIsoNodes.keySet().size() < srcGraph.eval().nodes().size()) {
			Node current = srcQ.poll();
			if (!srcIsoNodes.containsKey(current)) {
				isoNode x = new isoNode(current, srcLabel);
				srcLabel +=1;
				srcIsoNodes.put(current, x);
				srcCreatedIso.add(x);
			}else if (current.taggedWith(XCSG.ControlFlowLoopCondition)){
				isoNode loopHeader = srcIsoNodes.get(current);
				loopHeader.structure = XCSG.ControlFlowLoopCondition;
				srcCreatedIso.add(loopHeader);
			}
			for(Edge e : current.out().tagged("src_induced_edge")) {
				if (e.hasAttr(XCSG.conditionValue)) {
					if (e.getAttr(XCSG.conditionValue).toString().contains("true")) {
						srcQ.add(e.to());
					}else {
						falseNode = e.to();
					}
				}else {
					srcQ.add(e.to());
				}
			}
			srcQ.add(falseNode);
		}
		
		//setting the parent and children labels for each node 
		for (Node n : srcNodes) {
			isoNode currentIso = srcIsoNodes.get(n);
			AtlasSet<Edge> nIncoming = n.in().tagged("src_induced_edge");
			AtlasSet<Edge> nOutgoing = n.out().tagged("src_induced_edge");
			
			currentIso.constraint = nIncoming.size();
			
			for (Edge e : nIncoming) {
				isoNode tempParent = srcIsoNodes.get(e.from());
				currentIso.addToParents(tempParent.label);
			}
			
			for (Edge e : nOutgoing) {
				isoNode tempChild = srcIsoNodes.get(e.to());
				currentIso.addToChildren(tempChild.label);
			}
		}
		
		calculateNodeDepth(r, "src_induced_edge", srcIsoNodes);

		
		Node binRoot = binGraph.eval().roots().getFirst();
		AtlasSet<Edge> binRootOut = binRoot.out().tagged("bin_induced_edge");
		isoNode binR = new isoNode(binRoot, binLabel);
		binR.depth.add(0);
		
		binIsoNodes.put(binRoot, binR);
		binCreatedIso.add(binR);
		binLabel +=1;
		
		AtlasSet<Node> binNodes = binGraph.eval().nodes().tagged("bin_node");
		Queue<Node> binQ = new LinkedList<Node>();
		falseNode = null;
		for(Edge e : binRootOut) {
			if (e.hasAttr(XCSG.conditionValue)) {
				if (e.getAttr(XCSG.conditionValue).toString().contains("true")) {
					binQ.add(e.to());
				}else {
					falseNode = e.to();
				}
			}
		}
		binQ.add(falseNode);
		
		while(binIsoNodes.keySet().size() < binGraph.eval().nodes().size()) {
			Node current = binQ.poll();
			if (!binIsoNodes.containsKey(current)) {
				isoNode x = new isoNode(current, binLabel);
				binLabel +=1;
				binIsoNodes.put(current, x);
				binCreatedIso.add(x);
			}else if (current.taggedWith(XCSG.ControlFlowLoopCondition)){
				isoNode loopHeader = binIsoNodes.get(current);
				loopHeader.structure = XCSG.ControlFlowLoopCondition;
				binCreatedIso.add(loopHeader);
			}
			for(Edge e : current.out().tagged("bin_induced_edge")) {
				if (e.hasAttr(XCSG.conditionValue)) {
					if (e.getAttr(XCSG.conditionValue).toString().contains("true")) {
						binQ.add(e.to());
					}else {
						falseNode = e.to();
					}
				}else {
					binQ.add(e.to());
				}
			}
			binQ.add(falseNode);
		}
		
		//setting the parent and children labels for each node 
		for (Node n : binNodes) {
			isoNode currentIso = binIsoNodes.get(n);
			AtlasSet<Edge> nIncoming = n.in().tagged("bin_induced_edge");
			AtlasSet<Edge> nOutgoing = n.out().tagged("bin_induced_edge");
			
			currentIso.constraint = nIncoming.size();

			for (Edge e : nOutgoing) {
				isoNode tempChild = binIsoNodes.get(e.to());
				currentIso.addToChildren(tempChild.label);
			}
		}
		
		calculateNodeDepth(binR, "bin_induced_edge", binIsoNodes);
				
		for (int i = 0; i < srcCreatedIso.size(); i++) {
			isoNode s = srcCreatedIso.get(i);
			isoNode b = binCreatedIso.get(i);
			
			ArrayList<Integer> sChildren = s.children;
			ArrayList<Integer> bChildren = b.children;
			ArrayList<Integer> sParents = s.parents;
			ArrayList<Integer> bParents = b.parents;
			ArrayList<Integer> sDepth = s.depth;
			ArrayList<Integer> bDepth = b.depth;
			
			boolean childrenCheck = sChildren.containsAll(bChildren);
			boolean parentCheck = sParents.containsAll(bParents);
			boolean depthCheck = sDepth.containsAll(bDepth);
			
			if (childrenCheck && parentCheck && depthCheck) {
				System.out.println("iso");
			}
		}
		
		
	}
	
	private static class isoNode {
		private Node graphNode; 
		private ArrayList<Integer>children; 
		private ArrayList<Integer> parents;
		private ArrayList<Integer>height;
		private ArrayList<Integer>depth;
		private int label;
		private String structure;
		private long constraint; 
		
		public isoNode(Node g, int l) {
			this.graphNode = g;
			this.label = l;
			this.children = new ArrayList<Integer>();
			this.parents = new ArrayList<Integer>();
			this.depth = new ArrayList<Integer>();
		}
		
		public void addToChildren(int c) {
			this.children.add(c);
		}
		
		public void addToParents(int p) {
			this.parents.add(p);
		}
	}
	
	public static void calculateNodeDepth(isoNode root, String tag, Map<Node, isoNode> isoNodes) {
		
		Stack<isoNode> stack = new Stack<isoNode>();
		stack.push(root);
		
		while (!stack.isEmpty()) {
			isoNode v = stack.pop();
			AtlasSet<Edge> outEdges = v.graphNode.out().tagged(tag);
			
			for(Edge e : outEdges) {
				isoNode tempChild = isoNodes.get(e.to());
				tempChild.constraint -=1;
				
				for (int x : v.depth) {
					tempChild.depth.add(x+1);
				}
				
				if (tempChild.constraint == 0) {
					stack.push(tempChild);
				}
			}
			
		}
	}
	
	public static void isoNodeCreation() {
		
	}
}
