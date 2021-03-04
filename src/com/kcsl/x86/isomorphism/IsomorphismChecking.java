package com.kcsl.x86.isomorphism;

import com.ensoftcorp.atlas.core.db.graph.Edge;
import com.ensoftcorp.atlas.core.db.graph.Graph;
import com.ensoftcorp.atlas.core.db.graph.Node;
import com.ensoftcorp.atlas.core.db.set.AtlasSet;
import com.ensoftcorp.atlas.core.query.Q;
import com.ensoftcorp.atlas.core.query.Query;
import com.ensoftcorp.atlas.core.script.Common;
import com.ensoftcorp.atlas.core.xcsg.XCSG;
import com.ensoftcorp.atlas.ui.viewer.graph.SaveUtil;

import static com.kcsl.x86.Importer.my_cfg;
import static com.kcsl.x86.Importer.my_function;
import static com.kcsl.x86.static_function_transform.StaticFunctionChecking.*;
import static com.kcsl.x86.switch_transform.SwitchStatementChecking.*;
import static com.kcsl.x86.support.SupportMethods.*;

import java.io.BufferedWriter;
import java.io.File;
import java.io.FileWriter;
import java.io.IOException;
import java.util.ArrayList;
import java.util.Arrays;
import java.util.HashMap;
import java.util.LinkedList;
import java.util.Map;
import java.util.Queue;
import java.util.Stack;

import static com.kcsl.x86.subgraphs.SubGraphGenerator.*;

public class IsomorphismChecking {
	
	protected static final String graphPath = "/Users/RyanGoluch/Desktop/Masters_Work/slti_graphs/";
	
	public static Q createSrcGraph(String functionName) {
		
		Q staticSrcGraph = staticTransform(functionName);
		Q switchSrcGraph = switchTransform(functionName, staticSrcGraph);
		String name = switchSrcGraph.containers().nodes(XCSG.Function).eval().nodes().one().getAttr(XCSG.name).toString();
		Q scSrcGraph = singleSrcReturn(switchSrcGraph, name, 1);
		Q srcSubGraph = findSrcSubGraph(scSrcGraph);
				
		return srcSubGraph;
	}
	
	public static isoNodeResult isomorphismChecker(String functionName, int mode) {
		String srcName = functionName.substring(4);
				
		Q srcCheck = bcfg(srcName);
		if (srcCheck.eval().nodes().size() == 0) {
			isoNodeResult z = new isoNodeResult(false, 0, 0, "Binary only function: "+ functionName);
			return z;
		}
		
		Q srcGraph = null;
		Q binGraph = null;
		
		if (mode == 0) {
			srcGraph = createSrcGraph(srcName);
			binGraph = findSubGraph(functionName);
		}else {
			Q tempSrc = srcTransformedGraph(srcName);
			srcGraph = createReverseGraph(tempSrc, srcName, 0);
			
			Q tempBin = binTransformedGraph(functionName);
			binGraph = createReverseGraph(tempBin, functionName, 1);
		}
		
		if (srcGraph == null) {
			isoNodeResult z = new isoNodeResult(false, 0, binGraph.eval().nodes().size(), "Null Src Graph");
			return z;
		}
		
		if (binGraph.eval().nodes().size() == 0) {
			isoNodeResult z = new isoNodeResult(false, 0, 0, "Empty binary");
			return z;
		}
		
		Map<Node, isoNode> srcIsoNodes = new HashMap<Node, isoNode>();
		Map<Node, isoNode> binIsoNodes = new HashMap<Node, isoNode>();
		
		ArrayList<isoNode> srcCreatedIso = new ArrayList<isoNode>();
		ArrayList<isoNode> binCreatedIso = new ArrayList<isoNode>();

		int srcLabel = 1; 
		
		AtlasSet<Node> srcLoopHeaders = srcGraph.eval().nodes().tagged(XCSG.ControlFlowLoopCondition);
		AtlasSet<Node> binLoopHeaders = binGraph.eval().nodes().tagged(XCSG.ControlFlowLoopCondition);
		ArrayList<isoNode> srcLoops = new ArrayList<isoNode>();
		ArrayList<isoNode> binLoops = new ArrayList<isoNode>();
		
		
		//Sanity check that we have the same number of loops
		if (srcLoopHeaders.size() != binLoopHeaders.size()) {
			isoNodeResult z = new isoNodeResult(false, srcGraph.eval().nodes().size(), binGraph.eval().nodes().size(), "Loop header count mismatch");
			return z;
		}
		
//		for (Node n : binGraph.eval().nodes()) {
//			String nodeName = n.getAttr(XCSG.name).toString();
//			if (binGraph.eval().nodes().size() != 0) {
//				if (nodeName.contains("slti") || nodeName.contains("sltiu") || nodeName.contains("slt")) {
//					SaveUtil.saveGraph(new File(graphPath+"bin_"+srcName+"_cfg.png"), binGraph.eval());
//					SaveUtil.saveGraph(new File(graphPath+"src_"+srcName+"_iso.png"), srcGraph.eval());
//					Q srcCFG = bcfg(srcName);
//					SaveUtil.saveGraph(new File(graphPath+"src_"+srcName+"_cfg.png"), srcCFG.eval());
//					break;
//				}
//			}
//		}
		
		if (srcGraph.eval().nodes().tagged("src_node").size() != binGraph.eval().nodes().tagged("bin_node").size()) {
			isoNodeResult z = new isoNodeResult(false, srcGraph.eval().nodes().size(), binGraph.eval().nodes().size(), "Node count mismatch");
			return z;
		}
		
		for (Node l : srcLoopHeaders) {
			isoNode i = new isoNode(l, srcLabel);
			
			String nodeName = l.getAttr(XCSG.name).toString();
			if (mode == 1) {
				nodeName = nodeName.split("LABEL:")[0];
				nodeName += "\nREV_LABEL: "+srcLabel;
			}else {
				nodeName += "\nLABEL: "+srcLabel;
			}
			l.putAttr(XCSG.name, nodeName);
			
			i.structure = XCSG.ControlFlowLoopCondition;
			srcLabel +=1;
			srcIsoNodes.put(l, i);
			srcCreatedIso.add(i);
			srcLoops.add(i);
		}
		
		int binLabel = 1;
		//Handle binary graph 
		for (Node l : binLoopHeaders) {
			isoNode i = new isoNode(l, binLabel);
			
			String nodeName = l.getAttr(XCSG.name).toString();
			if (mode == 1) {
				nodeName = nodeName.split("LABEL:")[0];
				nodeName += "\nREV_LABEL: "+binLabel;
			}else {
				nodeName += "\nLABEL: "+binLabel;
			}
			l.putAttr(XCSG.name, nodeName);
			
			i.structure = XCSG.ControlFlowLoopCondition;
			binLabel +=1;
			binIsoNodes.put(l, i);			
			binCreatedIso.add(i);
			binLoops.add(i);
		}
		
		//Add exit nodes after loop headers 
		Node srcExit = srcGraph.eval().nodes().tagged("src_exit").getFirst();
		isoNode sExit = new isoNode(srcExit, srcLabel);
		
		String nodeName = srcExit.getAttr(XCSG.name).toString();
		if (mode == 1) {
			nodeName = nodeName.split("LABEL:")[0];
			nodeName += "\nREV_LABEL: "+srcLabel;
		}else {
			nodeName += "\nLABEL: "+srcLabel;
		}
		srcExit.putAttr(XCSG.name, nodeName);
		
		srcLabel +=1;
		srcIsoNodes.put(srcExit, sExit);
		srcCreatedIso.add(sExit);
		
		Node binExit = binGraph.eval().nodes().tagged("bin_exit").getFirst();
		isoNode bExit = new isoNode(binExit, binLabel);
		
		nodeName = binExit.getAttr(XCSG.name).toString();
		if (mode == 1) {
			nodeName = nodeName.split("LABEL:")[0];
			nodeName += "\nREV_LABEL: "+binLabel;
		}else {
			nodeName += "\nLABEL: "+binLabel;
		}
		binExit.putAttr(XCSG.name, nodeName);
		
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
			
			nodeName = srcRoot.getAttr(XCSG.name).toString();
			if (mode == 1) {
				nodeName = nodeName.split("LABEL:")[0];
				nodeName += "\nREV_LABEL: "+srcLabel;
			}else {
				nodeName += "\nLABEL: "+srcLabel;
			}
			srcRoot.putAttr(XCSG.name, nodeName);
			
			srcLabel +=1;
		}else {
			r = srcIsoNodes.get(srcRoot);
			r.depth.add(0);
		}
		
		createIsoNodes(srcGraph, 1, srcIsoNodes, srcCreatedIso, srcLabel, r, rootOut);
		

		Node binRoot = binGraph.eval().nodes().tagged(XCSG.controlFlowRoot).one();
		AtlasSet<Edge> binRootOut = binRoot.out().tagged("bin_induced_edge");
		isoNode binR = new isoNode(binRoot, binLabel);
		binR.depth.add(0);
		
		if (!binIsoNodes.containsKey(binRoot)) {
			binIsoNodes.put(binRoot, binR);
			binCreatedIso.add(binR);
			
			nodeName = binRoot.getAttr(XCSG.name).toString();
			if (mode == 1) {
				nodeName = nodeName.split("LABEL:")[0];
				nodeName += "\nREV_LABEL: "+binLabel;
			}else {
				nodeName += "\nLABEL: "+binLabel;
			}
			binRoot.putAttr(XCSG.name, nodeName);
			
			binLabel +=1;
		}else {
			binR = binIsoNodes.get(binRoot);
			binR.depth.add(0);
		}
		
		createIsoNodes(binGraph, 0, binIsoNodes, binCreatedIso, binLabel, binR, binRootOut);
		AtlasSet<Node> binNodes = binGraph.eval().nodes().tagged("bin_node");

		//Check to make sure loop headers are properly tagged
		for (int i = 0; i < srcLoops.size(); i++) {
			isoNode src = srcLoops.get(i);
			isoNode bin = binLoops.get(i);
			
			ArrayList<Node> srcChildren = new ArrayList<Node>();
			for (Node s : src.loopChildren) {
				srcChildren.add(s);
			}
			
			ArrayList<Node> binChildren = new ArrayList<Node>();
			for (Node s : bin.loopChildren) {
				binChildren.add(s);
			}
//			Node s1 = src.loopChildren.get(0);
//			Node s2 = src.loopChildren.get(1);
//			Node b1 = bin.loopChildren.get(0);
//			Node b2 = bin.loopChildren.get(1);
			
			ArrayList<String> sAttr = new ArrayList<String>();
			for (Node s : srcChildren) {
				sAttr.add(s.getAttr("child_id").toString());
			}
//			sAttr.add(s1.getAttr("child_id").toString());
//			sAttr.add(s2.getAttr("child_id").toString());
			
			ArrayList<String> bAttr = new ArrayList<String>();
			for (Node s : binChildren) {
				bAttr.add(s.getAttr("child_id").toString());
			}
//			bAttr.add(b1.getAttr("child_id").toString());
//			bAttr.add(b2.getAttr("child_id").toString());
			
			boolean checking = bAttr.containsAll(sAttr);
			if (!checking) {
				
				ArrayList<isoNode> bNodes = new ArrayList<isoNode>();
				for (Node b : binChildren) {
					isoNode gettingIso = binIsoNodes.get(b);
					bNodes.add(gettingIso);
				}
				
//				isoNode b1Node = binIsoNodes.get(b1);
//				isoNode b2Node = binIsoNodes.get(b2);
				bAttr.clear();
				
				for (isoNode currentIso : bNodes) {
					ArrayList<Node> gcNodes = new ArrayList<Node>();
					for (Node g : currentIso.loopChildren) {
						gcNodes.add(g);
						bAttr.add(g.getAttr("child_id").toString());
					}
					
					for (Node c : gcNodes) {
						String gcName = c.getAttr(XCSG.name).toString();
						
						if (bAttr.containsAll(sAttr) && gcName.contains(bin.graphNode.getAttr(XCSG.name).toString())) {
							int temp = currentIso.label;
							isoNode oldHeader = binIsoNodes.get(c);
							int parent = oldHeader.label;
							currentIso.label = parent;
							oldHeader.label = temp;
							
							loopRetagging(binCreatedIso, currentIso, oldHeader, binNodes, binIsoNodes);
							break;
						}
					}
				}
				
				
//				gcNodes = new ArrayList<Node>();
//				for (Node g : b2Node.loopChildren) {
//					gcNodes.add(g);
//					bAttr.add(g.getAttr("child_id").toString());
//				}
//				
//				for (Node c : gcNodes) {
//					String gcName = c.getAttr(XCSG.name).toString();
//					
//					if (bAttr.containsAll(sAttr) && gcName.contains(bin.graphNode.getAttr(XCSG.name).toString())) {
//						int temp = b1Node.label;
//						isoNode oldHeader = binIsoNodes.get(c);
//						int parent = oldHeader.label;
//						b1Node.label = parent;
//						oldHeader.label = temp;
//						
//						loopRetagging(binCreatedIso, b1Node, oldHeader, binNodes, binIsoNodes);
//						break;
//					}
//				}	
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
			}else {
				System.out.println("Failed at Source Label: "+s.label);
				System.out.println("Failed at Binary Label: "+b.label);
				break;
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
		String isoPath = "/Users/RyanGoluch/Desktop/Masters_Work/isomorphism_checking/iso_results_new_xinu.csv";
		File isoFile = new File(isoPath);
		BufferedWriter isoWriter = new BufferedWriter(new FileWriter(isoFile));
		isoWriter.write("Function Name, Iso Result, Src Node Count, Bin Node Count, Error\n");
		
		int trueCount = 0; 
		int falseCount = 0;
		int errorCount = 0;
		
		Q functions = Query.universe().nodesTaggedWithAll(XCSG.Function, "new_xinu");
		System.out.println("function size: "+functions.eval().nodes().size());
		for (Node function : functions.eval().nodes()) {
			String fName = function.getAttr(XCSG.name).toString();
			System.out.println("name: "+fName);

			if(fName.contains("setupStack") || fName.contains("test") || fName.contains("lexan") 
					|| fName.contains("enqueue") || fName.contains("insert") || fName.contains("dispatch")) {
//				System.out.println("skipped function: "+fName);
				continue;
			}
			
			isoNodeResult result = isomorphismChecker(fName,0);
			
//			Q binGraph = findSubGraph(fName);
//			for (Node n : binGraph.eval().nodes()) {
//				String nodeName = n.getAttr(XCSG.name).toString();
//				if (result.binSize != 0 && result.error != null && !result.error.contains("Binary only function: ")) {
//					if (nodeName.contains("slti") || nodeName.contains("sltiu") || nodeName.contains("slt")) {
//						if (result.error.contains("Binary only function: ")) {
//							System.out.println(fName);
//
//						}
//						result.error = "SLTI Function";
//						break;
//					}
//				}
//			}
			
			if (result.error == null) {
				if (result.result == true) {
					trueCount +=1;
				}else {
					falseCount +=1;
				}
				
				isoWriter.write(fName + "," + result.result + "," + result.srcSize + "," + result.binSize + "\n");
				isoWriter.flush();
			}else {
				if (result.binSize != 0 && result.error.equals("Node count mismatch") && result.binSize != result.srcSize) {
					errorCount +=1;
					isoWriter.write(fName + "," + result.result + "," + result.srcSize + "," + result.binSize + "," + result.error + "\n");
					isoWriter.flush();
				}
				else if (!result.error.contains("Binary only function: ") && !result.error.contains("SLTI Function") && result.binSize != 0) {
					errorCount +=1;
					isoWriter.write(fName + "," + result.result + "," + result.srcSize + "," + result.binSize + "," + result.error + "\n");
					isoWriter.flush();
				}
			}
		}
		
		isoWriter.write("\n");
		isoWriter.write("True Count, False Count, Error Count\n");
		isoWriter.write(trueCount +","+falseCount+","+errorCount);
		isoWriter.flush();
		
		isoWriter.close();
		
	}
	
	public static void countGenerator() throws IOException {
		String isoPath = "/Users/RyanGoluch/Desktop/Masters_Work/isomorphism_checking/iso_sub_new_counts1.csv";
		File isoFile = new File(isoPath);
		BufferedWriter isoWriter = new BufferedWriter(new FileWriter(isoFile));
		isoWriter.write("Function Name, Iso Result, Src Node Count, Bin Node Count, Error, SLT Count\n");
		
		int trueCount = 0; 
		int falseCount = 0;
		int sltCount = 0;
		int loopHeaderCount = 0;
		int nodeCountMismatch = 0;
		int binOnly = 0;
		int binEmpty = 0;
		
		Q functions = Query.universe().nodesTaggedWithAll(XCSG.Function, "new_xinu");
		for (Node function : functions.eval().nodes()) {
			String fName = function.getAttr(XCSG.name).toString();
			System.out.println("name: "+fName);

			if(fName.contains("setupStack") || fName.contains("test") || fName.contains("lexan") 
					|| fName.contains("enqueue") || fName.contains("insert") || fName.contains("dispatch") 
					|| fName.contains("x_mount") || fName.contains("x_rls")) {
				continue;
			}
			
			isoNodeResult result = isomorphismChecker(fName,0);
			
			int sltNodeCounter = 0; 
			Q binGraph = findSubGraph(fName);
			for (Node n : binGraph.eval().nodes()) {
				String nodeName = n.getAttr(XCSG.name).toString();
				if (result.binSize != 0 && result.error != null && result.error.equals("Node count mismatch")) {
					if (nodeName.contains("slti") || nodeName.contains("sltiu") || nodeName.contains("slt")) {
//							|| nodeName.contains("sltiu") || nodeName.contains("slt")) {
//						if (result.error.contains("Binary only function: ")) {
//							System.out.println(fName);
//
//						}
						result.error = "SLT Function";
						sltNodeCounter +=1;
					}
				}
			}

			if (result.error == null) {
				if (result.result == true) {
					trueCount +=1;
				}else {
					falseCount +=1;
				}
				isoWriter.write(fName + "," + result.result + "," + result.srcSize + "," + result.binSize + "\n");
				isoWriter.flush();
			}else {
				if (result.error.equals("Node count mismatch")) {
					nodeCountMismatch +=1;
					isoWriter.write(fName + "," + result.result + "," + result.srcSize + "," + result.binSize + "," + result.error + "\n");
					isoWriter.flush();
				}
//				else if (result.error.contains("Binary only function: ")) {
//					binOnly +=1;
//					isoWriter.write(fName + "," + result.result + "," + result.srcSize + "," + result.binSize + "," + result.error + "\n");
//					isoWriter.flush();
//				}
				else if (result.error.contains("SLT Function")) {
					sltCount +=1;
					isoWriter.write(fName + "," + result.result + "," + result.srcSize + "," + result.binSize + "," + result.error + "," + sltNodeCounter + "\n");
					isoWriter.flush();
				}
//				else if (result.error.contains("Empty binary")) {
//					binEmpty +=1;
//					isoWriter.write(fName + "," + result.result + "," + result.srcSize + "," + result.binSize + "," + result.error + "\n");
//					isoWriter.flush();
//				}
				else if (result.error.contains("Loop header count mismatch")) {
					loopHeaderCount +=1;
					isoWriter.write(fName + "," + result.result + "," + result.srcSize + "," + result.binSize + "," + result.error + "\n");
					isoWriter.flush();
				}
			}
		}
		
		isoWriter.write("\n");
		isoWriter.write("True Count, False Count, SLT Functions, Loop Header Mismatch, Node Count Mismatch, Empty Binary, Binary Only\n");
		isoWriter.write(trueCount +","+falseCount+","+ sltCount + "," + loopHeaderCount + "," + nodeCountMismatch + "," + binEmpty + "," + binOnly);
		isoWriter.flush();
		
		isoWriter.close();
		
	}
	
	public static void sltCounter() {
		
		Q functions = Query.universe().nodesTaggedWithAll(XCSG.Function, "class_xinu");
		for (Node function : functions.eval().nodes()) {
			String fName = function.getAttr(XCSG.name).toString();

			if(fName.contains("setupStack") || fName.contains("test") || fName.contains("lexan") 
					|| fName.contains("enqueue") || fName.contains("insert") || fName.contains("dispatch")) {
				continue;
			}
			
			Q binGraph = findSubGraph(fName);
			int sltCount = 0;
			for (Node n : binGraph.eval().nodes()) {
				String nodeName = n.getAttr(XCSG.name).toString();
				if (nodeName.contains("slti") || nodeName.contains("sltiu") || nodeName.contains("slt")) {
					System.out.println(fName);
					break;
				}
			}
		}
	}
	
	private static class isoNode {
		private Node graphNode; 
		private ArrayList<Integer>children; 
		private ArrayList<Node>loopChildren; 
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
			this.loopChildren = new ArrayList<Node>();
		}
		
		public void addToChildren(int c) {
			this.children.add(c);
		}
		
		public void addToParents(int p) {
			this.parents.add(p);
		}
	}
	
	public static void loopRetagging(ArrayList<isoNode> binCreatedIso, isoNode b1Node, isoNode oldHeader, AtlasSet<Node> binNodes, Map<Node, isoNode> binIsoNodes) {
		
		for (isoNode b : binCreatedIso) {
			b.children.clear();
			b.parents.clear();
			b.depth.clear();
		}

		Iterable<String> oldChildTags = b1Node.graphNode.tagsI();
		Iterable<String> oldParentTags = oldHeader.graphNode.tagsI();
		
		for (String s : oldChildTags) {
			b1Node.graphNode.untag(s);
		}
		
		for (String s : oldParentTags) {
			oldHeader.graphNode.untag(s);
			b1Node.graphNode.tag(s);
		}
		
		for (String s : oldChildTags) {
			oldHeader.graphNode.tag(s);
		}
		
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
		
		isoNode binR = binIsoNodes.get(b1Node.graphNode);
		binR.depth.add(0);
		
		calculateNodeDepth(binR, "bin_induced_edge", binIsoNodes);
		
		for (int x = 0; x < binCreatedIso.size(); x++) {
			for (int y = x + 1; y < binCreatedIso.size(); y++) {
				isoNode checkingB = binCreatedIso.get(x);
				isoNode nextNode = binCreatedIso.get(y);
				
				if (checkingB.maxDepth > nextNode.maxDepth) {
					binCreatedIso.set(y, checkingB);
					binCreatedIso.set(x, nextNode);
				}
				if (checkingB.maxDepth == nextNode.maxDepth && nextNode.graphNode.taggedWith(XCSG.controlFlowRoot)) {
					binCreatedIso.set(y, checkingB);
					binCreatedIso.set(x, nextNode);
				}
			}
		}
	}
	
	public static void createIsoNodes(Q graph, int flag, Map<Node, isoNode> isoNodes, ArrayList<isoNode> createdIso, int label, isoNode r, AtlasSet<Edge> rootOut) {
		
		String nodeTag = null;
		String edgeTag = null;
		
		if (flag == 1) {
			nodeTag = "src_node";
			edgeTag = "src_induced_edge";
		}else {
			nodeTag = "bin_node";
			edgeTag = "bin_induced_edge";
		}
		
		AtlasSet<Node> srcNodes = graph.eval().nodes().tagged(nodeTag);
		Queue<Node> srcQ = new LinkedList<Node>();
		Node falseNode = null;
		for(Edge e : rootOut) {
			srcQ.add(e.to());
		}
		long size = graph.eval().nodes().size();
		while(isoNodes.keySet().size() < graph.eval().nodes().size()) {
			Node current = srcQ.poll();
			if (!isoNodes.containsKey(current) && current != null) {
				isoNode x = new isoNode(current, label);
				
				String nodeName = current.getAttr(XCSG.name).toString();
				if (current.taggedWith("reversed_graph") && !nodeName.contains("REV_LABEL")) {
					nodeName = nodeName.split("LABEL:")[0];
					nodeName += "\nREV_LABEL: "+label;
				}else {
					nodeName += "\nLABEL: "+label;
				}
				current.putAttr(XCSG.name, nodeName);
				
				label +=1;
				isoNodes.put(current, x);
				createdIso.add(x);
			}else if (current.taggedWith(XCSG.ControlFlowLoopCondition) && !isoNodes.containsKey(current)){
				isoNode loopHeader = isoNodes.get(current);
				loopHeader.structure = XCSG.ControlFlowLoopCondition;
				createdIso.add(loopHeader);
			}
			for(Edge e : current.out().tagged(edgeTag)) {
				srcQ.add(e.to());
			}
		}
		
		//setting the parent and children labels for each node 
		for (Node n : srcNodes) {
			isoNode currentIso = isoNodes.get(n);
			AtlasSet<Edge> nIncoming = n.in().tagged(edgeTag);
			AtlasSet<Edge> nOutgoing = n.out().tagged(edgeTag);
			
			currentIso.constraint = nIncoming.size();
			
			for (Edge e : nIncoming) {
				isoNode tempParent = isoNodes.get(e.from());
				currentIso.addToParents(tempParent.label);
				tempParent.loopChildren.add(currentIso.graphNode);
			}
			for (Edge e : nOutgoing) {
				isoNode tempChild = isoNodes.get(e.to());
				currentIso.addToChildren(tempChild.label);
			}
			
			if (currentIso.graphNode.taggedWith(XCSG.ControlFlowCondition)) {
				currentIso.graphNode.putAttr("child_id", XCSG.ControlFlowCondition);
			}else if (currentIso.graphNode.taggedWith(XCSG.controlFlowExitPoint)){
				currentIso.graphNode.putAttr("child_id", XCSG.controlFlowExitPoint);
			}else {
				currentIso.graphNode.putAttr("child_id", XCSG.ControlFlow_Node);
			}
		}
		
		calculateNodeDepth(r, edgeTag, isoNodes);
		
		for (int x = 0; x < createdIso.size(); x++) {
			for (int y = x + 1; y < createdIso.size(); y++) {
				isoNode checking = createdIso.get(x);
				isoNode nextNode = createdIso.get(y);
				
				if (checking.maxDepth > nextNode.maxDepth) {
					createdIso.set(y, checking);
					createdIso.set(x, nextNode);
				}
			}
		}
		
//		return srcNodes;
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
	
	public static Q createReverseGraph(Q originalGraph, String originalName, int flag) {
		Node originalRoot = originalGraph.eval().nodes().tagged(XCSG.controlFlowRoot).one();
		Node originalExit = originalGraph.eval().nodes().tagged("single_exit").getFirst();
		
		String tag = null;
		String edgeTag = null;
		if (flag == 1) {
			tag = "bin_node";
			edgeTag = "bin_induced_edge";
		}else {
			tag = "src_node";
			edgeTag = "src_induced_edge";
		}
		
		Map<Node, Node> recreatedNodes = new HashMap<Node, Node>();
		
		Node newFunc = Graph.U.createNode();
		newFunc.putAttr(XCSG.name, "reversed_"+originalName);
		newFunc.tag(XCSG.Function);
//		newFunc.tag("reversed_graph");
		
		for (Node n : originalGraph.eval().nodes().tagged(tag)) {
			for (Edge e : n.out().tagged(edgeTag)) {
				Node from = e.from();
				Node to = e.to();
				Node newFrom = null;
				Node newTo = null;
				
				if (recreatedNodes.get(to) == null) {
					newFrom = Graph.U.createNode();
					newFrom.tag("reversed_graph");
					Iterable<String> i = e.to().tagsI();
					
					for (String s : i) {
						newFrom.tag(s);
					}
					newFrom.putAllAttr(e.to().attr());
					Edge e1 = Graph.U.createEdge(newFunc, newFrom);
					e1.tag(XCSG.Contains);
					
					recreatedNodes.put(to, newFrom);
				}else {
					newFrom = recreatedNodes.get(to);
				}
				
				if (recreatedNodes.get(from) == null) {
					newTo = Graph.U.createNode();
					newTo.tag("reversed_graph");
					Iterable<String> i = e.from().tagsI();
					
					for (String s : i) {
						newTo.tag(s);
					}
					newTo.putAllAttr(e.from().attr());
					Edge e2 = Graph.U.createEdge(newFunc, newTo);
					e2.tag(XCSG.Contains);
					
					recreatedNodes.put(from, newTo);
				}else {
					newTo = recreatedNodes.get(from);
				}
				
				
				Edge e3 = Graph.U.createEdge(newFrom, newTo);
				Iterable<String> i = e.tagsI();
				for (String s : i) {
					e3.tag(s);
				}
				e3.tag("reversed_edge");
				e3.putAllAttr(e.attr());
			}
		}
		
		Node newRoot = recreatedNodes.get(originalRoot);
		newRoot.untag(XCSG.controlFlowRoot);
		newRoot.tag(XCSG.controlFlowExitPoint);
		newRoot.tag("single_exit");
		if (flag == 1) {
			newRoot.tag("bin_exit");
		}else {
			newRoot.tag("src_exit");
		}
		
		Node newExit = recreatedNodes.get(originalExit);
		newExit.tag(XCSG.controlFlowRoot);
		newExit.untag(XCSG.controlFlowExitPoint);
		newExit.untag("single_exit");
		if (flag == 1) {
			newExit.untag("bin_exit");
		}else {
			newExit.untag("src_exit");
		}
		
		Q x = my_function(newFunc.getAttr(XCSG.name).toString());
		Q reversedGraph = x.contained().nodes("reversed_graph").induce(Query.universe().edges("reversed_edge"));
		
		return reversedGraph;
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
