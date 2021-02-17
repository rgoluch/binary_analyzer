package com.kcsl.x86.isomorphism;

import com.ensoftcorp.atlas.core.db.graph.Edge;
import com.ensoftcorp.atlas.core.db.graph.Graph;
import com.ensoftcorp.atlas.core.db.graph.Node;
import com.ensoftcorp.atlas.core.db.set.AtlasSet;
import com.ensoftcorp.atlas.core.query.Q;
import com.ensoftcorp.atlas.core.query.Query;
import com.ensoftcorp.atlas.core.script.Common;
import com.ensoftcorp.atlas.core.xcsg.XCSG;

import static com.kcsl.x86.static_function_transform.StaticFunctionChecking.*;
import static com.kcsl.x86.switch_transform.SwitchStatementChecking.*;
import static com.kcsl.x86.support.SupportMethods.*;

import java.io.BufferedWriter;
import java.io.File;
import java.io.FileWriter;
import java.io.IOException;
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
	
	public static isoNodeResult isomorphismChecker(String functionName) {
		String srcName = functionName.substring(4);
				
		Q srcCheck = bcfg(srcName);
		if (srcCheck.eval().nodes().size() == 0) {
			isoNodeResult z = new isoNodeResult(false, 0, 0, "Binary only function: "+ functionName);
			return z;
		}
		
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
			isoNodeResult z = new isoNodeResult(false, srcGraph.eval().nodes().size(), binGraph.eval().nodes().size(), "Loop header count mismatch");
			return z;
		}

		if (srcGraph.eval().nodes().tagged("src_node").size() != binGraph.eval().nodes().tagged("bin_node").size()) {
			isoNodeResult z = new isoNodeResult(false, srcGraph.eval().nodes().size(), binGraph.eval().nodes().size(), "Node count mismatch");
			return z;
		}
		
		for (Node l : srcLoopHeaders) {
			isoNode i = new isoNode(l, srcLabel);
			i.structure = XCSG.ControlFlowLoopCondition;
			srcLabel +=1;
			srcIsoNodes.put(l, i);
			srcCreatedIso.add(i);
		}
		
		int binLabel = 1;
		//Handle binary graph 
		for (Node l : binLoopHeaders) {
			isoNode i = new isoNode(l, binLabel);
			i.structure = XCSG.ControlFlowLoopCondition;
			binLabel +=1;
			binIsoNodes.put(l, i);			
			binCreatedIso.add(i);
		}
		
		//Add exit nodes after loop headers 
		Node srcExit = srcGraph.eval().nodes().tagged("src_exit").getFirst();
		isoNode sExit = new isoNode(srcExit, srcLabel);
		srcLabel +=1;
		srcIsoNodes.put(srcExit, sExit);
		srcCreatedIso.add(sExit);
		
		Node binExit = binGraph.eval().nodes().tagged("bin_exit").getFirst();
		isoNode bExit = new isoNode(binExit, binLabel);
		binLabel +=1;
		binIsoNodes.put(binExit, bExit);
		binCreatedIso.add(bExit);
		
		
		//Handle source graph nodes
		Node srcRoot = srcGraph.eval().nodes().tagged(XCSG.controlFlowRoot).one();
		AtlasSet<Edge> rootOut = srcRoot.out().tagged("src_induced_edge");
		isoNode r = new isoNode(srcRoot, srcLabel);
		r.depth.add(0);
		
		if (!srcIsoNodes.containsKey(srcRoot)) {
			srcIsoNodes.put(srcRoot, r);
			srcCreatedIso.add(r);
			srcLabel +=1;
		}
		
		
		AtlasSet<Node> srcNodes = srcGraph.eval().nodes().tagged("src_node");
		Queue<Node> srcQ = new LinkedList<Node>();
		Node falseNode = null;
		for(Edge e : rootOut) {
			srcQ.add(e.to());
		}
		
		while(srcIsoNodes.keySet().size() < srcGraph.eval().nodes().size()) {
			Node current = srcQ.poll();
			if (!srcIsoNodes.containsKey(current) && current != null) {
				isoNode x = new isoNode(current, srcLabel);
				srcLabel +=1;
				srcIsoNodes.put(current, x);
				srcCreatedIso.add(x);
			}else if (current.taggedWith(XCSG.ControlFlowLoopCondition) && !srcIsoNodes.containsKey(current)){
				isoNode loopHeader = srcIsoNodes.get(current);
				loopHeader.structure = XCSG.ControlFlowLoopCondition;
				srcCreatedIso.add(loopHeader);
			}
			for(Edge e : current.out().tagged("src_induced_edge")) {
				srcQ.add(e.to());
			}
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
		
		for (int x = 0; x < srcCreatedIso.size(); x++) {
			for (int y = x + 1; y < srcCreatedIso.size(); y++) {
				isoNode checking = srcCreatedIso.get(x);
				isoNode nextNode = srcCreatedIso.get(y);
				
				if (checking.maxDepth > nextNode.maxDepth) {
					srcCreatedIso.set(y, checking);
					srcCreatedIso.set(x, nextNode);
				}
			}
		}

		
		Node binRoot = binGraph.eval().nodes().tagged(XCSG.controlFlowRoot).one();
		AtlasSet<Edge> binRootOut = binRoot.out().tagged("bin_induced_edge");
		isoNode binR = new isoNode(binRoot, binLabel);
		binR.depth.add(0);
		
		if (!binIsoNodes.containsKey(binRoot)) {
			binIsoNodes.put(binRoot, binR);
			binCreatedIso.add(binR);
			binLabel +=1;
		}
		
		
		AtlasSet<Node> binNodes = binGraph.eval().nodes().tagged("bin_node");
		Queue<Node> binQ = new LinkedList<Node>();
		falseNode = null;
		for(Edge e : binRootOut) {
			binQ.add(e.to());
		}
		
		while(binIsoNodes.keySet().size() < binGraph.eval().nodes().size()) {
			Node current = binQ.poll();
			if (!binIsoNodes.containsKey(current)) {
				isoNode x = new isoNode(current, binLabel);
				binLabel +=1;
				binIsoNodes.put(current, x);
				binCreatedIso.add(x);
			}else if (current.taggedWith(XCSG.ControlFlowLoopCondition) && !binIsoNodes.containsKey(current)){
				isoNode loopHeader = binIsoNodes.get(current);
				loopHeader.structure = XCSG.ControlFlowLoopCondition;
				binCreatedIso.add(loopHeader);
			}
			for(Edge e : current.out().tagged("bin_induced_edge")) {
				binQ.add(e.to());
			}
		}
		
		//setting the parent and children labels for each node 
		for (Node n : binNodes) {
			isoNode currentIso = binIsoNodes.get(n);
			AtlasSet<Edge> nIncoming = n.in().tagged("bin_induced_edge");
			AtlasSet<Edge> nOutgoing = n.out().tagged("bin_induced_edge");
			
			currentIso.constraint = nIncoming.size();
			
			for (Edge e : nIncoming) {
				isoNode tempParent = binIsoNodes.get(e.from());
				currentIso.addToParents(tempParent.label);
			}

			for (Edge e : nOutgoing) {
				isoNode tempChild = binIsoNodes.get(e.to());
				currentIso.addToChildren(tempChild.label);
			}
		}
		
		calculateNodeDepth(binR, "bin_induced_edge", binIsoNodes);
		
		for (int x = 0; x < binCreatedIso.size(); x++) {
			for (int y = x + 1; y < binCreatedIso.size(); y++) {
				isoNode checking = binCreatedIso.get(x);
				isoNode nextNode = binCreatedIso.get(y);
				
				if (checking.maxDepth > nextNode.maxDepth) {
					binCreatedIso.set(y, checking);
					binCreatedIso.set(x, nextNode);
				}
			}
		}
		
		long isoCount = 0; 
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
				isoCount +=1;
			}
		}
		
		boolean result;
		result = false;
		if (isoCount == srcGraph.eval().nodes().tagged("src_node").size()) {
			result = true;
		}
		isoNodeResult g = new isoNodeResult(result, srcGraph.eval().nodes().size(), binGraph.eval().nodes().size(), null);
		return g;
	}
	
	public static void checkAllIso() throws IOException {
		String isoPath = "/Users/RyanGoluch/Desktop/Masters_Work/isomorphism_checking/iso_results.csv";
		File isoFile = new File(isoPath);
		BufferedWriter isoWriter = new BufferedWriter(new FileWriter(isoFile));
		isoWriter.write("Function Name, Iso Result, Src Node Count, Bin Node Count, Error\n");
		
		int trueCount = 0; 
		int falseCount = 0;
		int errorCount = 0;
		
		Q functions = Query.universe().nodesTaggedWithAll(XCSG.Function, "new_xinu");
		for (Node function : functions.eval().nodes()) {
			String fName = function.getAttr(XCSG.name).toString();
			System.out.println("name: "+fName);

			if(fName.contains("setupStack") || fName.contains("test") || fName.contains("lexan") 
					|| fName.contains("enqueue") || fName.contains("insert") || fName.contains("dispatch")) {
				System.out.println("skipped function: "+fName);
				continue;
			}
			
			isoNodeResult result = isomorphismChecker(fName);
			if (result.error == null) {
				if (result.result == true) {
					trueCount +=1;
				}else {
					falseCount +=1;
				}
				
				isoWriter.write(fName + "," + result.result + "," + result.srcSize + "," + result.binSize + "\n");
				isoWriter.flush();
			}else {
				errorCount +=1;
				isoWriter.write(fName + "," + result.result + "," + result.srcSize + "," + result.binSize + "," + result.error + "\n");
				isoWriter.flush();
			}
		}
		
		isoWriter.write("\n");
		isoWriter.write("True Count, False Count, Error Count\n");
		isoWriter.write(trueCount +","+falseCount+","+errorCount);
		isoWriter.flush();
		
		isoWriter.close();
		
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
		private int maxDepth;
		
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
		ArrayList<isoNode> depthList = new ArrayList<isoNode>();
		
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
					depthList.add(tempChild);
				}
			}
			
		}
		
		for (isoNode r : depthList) {
			ArrayList<Integer> depths = r.depth;
			int maxDepth = 0; 
			
			for (int i : depths) {
				if (i > maxDepth) {
					maxDepth = i;
				}
			}
			r.maxDepth = maxDepth;
		}
	}
	
	public static void isoNodeCreation() {
		
	}
	
	private static class isoNodeResult{
		private boolean result;
		private long srcSize; 
		private long binSize;
		private String error; 
		
		public isoNodeResult(boolean r, long s, long b, String e) {
			this.result = r;
			this.binSize = b;
			this.srcSize = s;
			this.error = e;
		}
	
	}
}
