package com.kcsl.x86.isomorphism;

import com.ensoftcorp.atlas.core.db.graph.Edge;
import com.ensoftcorp.atlas.core.db.graph.Graph;
import com.ensoftcorp.atlas.core.db.graph.Node;
import com.ensoftcorp.atlas.core.db.set.AtlasSet;
import com.ensoftcorp.atlas.core.query.Q;
import com.ensoftcorp.atlas.core.query.Query;
import com.ensoftcorp.atlas.core.markup.Markup;
import com.ensoftcorp.atlas.core.markup.MarkupProperty;
import com.ensoftcorp.atlas.core.script.Common;
import com.ensoftcorp.atlas.core.xcsg.XCSG;
import com.ensoftcorp.atlas.ui.viewer.graph.DisplayUtil;
import com.ensoftcorp.atlas.ui.viewer.graph.SaveUtil;
import com.kcsl.paths.transforms.DAGTransform;

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
import org.eclipse.swt.graphics.Color;

import static com.kcsl.x86.subgraphs.SubGraphGenerator.*;

public class IsomorphismChecking {
	
	protected static final String graphPath = "/Users/RyanGoluch/Desktop/Masters_Work/final_result_testing/";
	
	public static Q createSrcGraph(String functionName) {
		
//		if (functionName.contains("create")) {
//			System.out.println("here");
//		}
		
		Q staticSrcGraph = staticTransform(functionName);
		Q switchSrcGraph = switchTransform(functionName, staticSrcGraph);
		String name = switchSrcGraph.containers().nodes(XCSG.Function).eval().nodes().one().getAttr(XCSG.name).toString();
		
		if (name.contains("switch_transform_")) {
			name = name.split("_")[2];
		}
		
		Q scSrcGraph = singleSrcReturn(switchSrcGraph, name, 1);
		Q srcSubGraph = findSrcSubGraph(scSrcGraph);
				
		return srcSubGraph;
	}
	
	public static isoNodeResult isomorphismChecker(String functionName, int mode) {
		String srcName = "";
		if (functionName.contains("ppc_") || functionName.contains("sym_")){
			srcName = functionName.substring(4);
		}else {
			srcName = functionName.substring(6);
		}
				
		Q srcCheck = bcfg(srcName);
		if (srcCheck.eval().nodes().size() == 0) {
			isoNodeResult z = new isoNodeResult(false, 0, 0, "Binary only function: "+ functionName, 0, 0, null, null);
			return z;
		}
		
		Q srcGraph = null;
		Q binGraph = null;
		Q sCFG = bcfg(srcName);
		Q bCFG = bcfg(functionName);
		
		if (mode == 0) {
			DAGTransform d = new DAGTransform();
			srcGraph = createSrcGraph(srcName);
			
			if (functionName.contains("login")) {
				System.out.println("here");
			}
			
			binGraph = findSubGraph(functionName);
		}else {
			Q tempSrc = srcTransformedGraph(srcName);
			if (tempSrc.eval().nodes().size() == 0 || tempSrc.eval().nodes().size() == 1) {
				isoNodeResult z = new isoNodeResult(false, 0, 0, "Single node src", 0, 0, null, null);
				return z;
			}
			srcGraph = bcfg(srcName);		
			Q tempBin = binTransformedGraph(functionName);
			binGraph = bcfg(functionName);
			
			if ((int) binGraph.nodes(XCSG.ControlFlowCondition).eval().nodes().size() == 0 || (int) srcGraph.nodes(XCSG.ControlFlowCondition).eval().nodes().size() == 0) {
				System.out.println("checking2: "+functionName);
				String msg = "Empty binary";
				if (srcGraph.nodes(XCSG.ControlFlowCondition).eval().nodes().size() > 0) {
					msg = "Src Condition, Linear Binary";
				}else if (srcGraph.nodes(XCSG.ControlFlowCondition).eval().nodes().size() == 0 && srcGraph.eval().nodes().size() > 0 && 
						binGraph.eval().nodes().size() > 0) {
					msg = "Linear src function : Linear binary";
				}
				
				isoNodeResult z = new isoNodeResult(false, 0, 0, msg, 0, 0, null, null);
				return z;
			}
			
			srcGraph = createReverseGraph(tempSrc, srcName, 0);			
			binGraph = createReverseGraph(tempBin, functionName, 1);
		}
		
		if (srcGraph == null) {
			isoNodeResult z = new isoNodeResult(false, 0, binGraph.eval().nodes().size(), "Null Src Graph", 0, 0, null, null);
			return z;
		}

		if ( (long)bCFG.nodes(XCSG.ControlFlowCondition).eval().nodes().size() == (long)0 || (long)sCFG.nodes(XCSG.ControlFlowCondition).eval().nodes().size() == (long)0) {
			
			String msg = "Empty binary";
			if (srcGraph.nodes(XCSG.ControlFlowCondition).eval().nodes().size() > 0) {
				msg = "Src Condition : Linear Binary";
			}else if (sCFG.nodes(XCSG.ControlFlowCondition).eval().nodes().size() == 0 && sCFG.eval().nodes().size() > 0 && 
					bCFG.eval().nodes().size() > 0) {
				msg = "Linear src function : Linear binary";
			}
			isoNodeResult z = new isoNodeResult(false, 0, 0, msg, 0, 0, null, null);
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
		
		String message = "";
		
		//Sanity check that we have the same number of loops
		if (srcLoopHeaders.size() != binLoopHeaders.size()) {
			message += "Loop header count mismatch-";
//			isoNodeResult z = new isoNodeResult(false, srcGraph.eval().nodes().size(), binGraph.eval().nodes().size(), "Loop header count mismatch", 0, 0, null, null);
//			return z;
		}

		if (srcGraph.eval().nodes().tagged("src_node").size() != binGraph.eval().nodes().tagged("bin_node").size()) {
			message += "Node count mismatch-";
//			isoNodeResult z = new isoNodeResult(false, srcGraph.eval().nodes().size(), binGraph.eval().nodes().size(), "Node count mismatch", 0, 0, null, null);
//			return z;
		}
		
		//Add exit nodes after loop headers 
		Node srcExit = srcGraph.eval().nodes().tagged("src_exit").getFirst();
		isoNode sExit = new isoNode(srcExit, srcLabel);
		
		String nodeName = srcExit.getAttr(XCSG.name).toString();
		if (mode == 0) {
			nodeName += "\nLABEL: "+srcLabel;
		}
		srcExit.putAttr(XCSG.name, nodeName);
		
		srcLabel +=1;
		srcIsoNodes.put(srcExit, sExit);
		srcCreatedIso.add(sExit);
		
		for (Node l : srcLoopHeaders) {
			isoNode i = new isoNode(l, srcLabel);
			
			nodeName = l.getAttr(XCSG.name).toString();
			if (mode == 0) {
				nodeName += "\nLABEL: "+srcLabel;
			}
			l.putAttr(XCSG.name, nodeName);
			
			i.structure = XCSG.ControlFlowLoopCondition;
			srcLabel +=1;
			srcIsoNodes.put(l, i);
			srcCreatedIso.add(i);
			srcLoops.add(i);
		}
		
		AtlasSet<Node> tails = srcGraph.eval().nodes().tagged("src_loopback_tail");
		for (Node l : tails) {
			isoNode i = new isoNode(l, srcLabel);
			
			nodeName = l.getAttr(XCSG.name).toString();
			if (mode == 0) {
				nodeName += "\nLABEL: "+srcLabel;
			}
			l.putAttr(XCSG.name, nodeName);
			
			srcLabel +=1;
			srcIsoNodes.put(l, i);
			srcCreatedIso.add(i);
		}
		
		
		int binLabel = 1;
		Node binExit = binGraph.eval().nodes().tagged("bin_exit").getFirst();
		isoNode bExit = new isoNode(binExit, binLabel);
		
		nodeName = binExit.getAttr(XCSG.name).toString();
		if (mode == 0) {
			nodeName += "\nLABEL: "+binLabel;
		}
		binExit.putAttr(XCSG.name, nodeName);
		
		binLabel +=1;
		binIsoNodes.put(binExit, bExit);
		binCreatedIso.add(bExit);
		
		//Handle binary graph 
		for (Node l : binLoopHeaders) {
			isoNode i = new isoNode(l, binLabel);
			
			nodeName = l.getAttr(XCSG.name).toString();
			if (mode == 0) {
				nodeName += "\nLABEL: "+binLabel;
			}
			l.putAttr(XCSG.name, nodeName);
			
			i.structure = XCSG.ControlFlowLoopCondition;
			binLabel +=1;
			binIsoNodes.put(l, i);			
			binCreatedIso.add(i);
			binLoops.add(i);
		}
		
		tails = binGraph.eval().nodes().tagged("bin_loopback_tail");
		for (Node l : tails) {
			isoNode i = new isoNode(l, binLabel);
			
			nodeName = l.getAttr(XCSG.name).toString();
			if (mode == 0) {
				nodeName += "\nLABEL: "+binLabel;
			}
			l.putAttr(XCSG.name, nodeName);
			
			binLabel +=1;
			binIsoNodes.put(l, i);
			binCreatedIso.add(i);
		}
		
		
		//Handle source graph nodes
		Node srcRoot = srcGraph.eval().nodes().tagged(XCSG.controlFlowRoot).one();
		AtlasSet<Edge> rootOut = srcRoot.out().tagged("src_induced_edge");
		isoNode r = new isoNode(srcRoot, srcLabel);
		r.depth.add(0);
		
		if (!srcIsoNodes.containsKey(srcRoot)) {
			srcIsoNodes.put(srcRoot, r);
			srcCreatedIso.add(r);
			
			nodeName = srcRoot.getAttr(XCSG.name).toString();
			if (mode == 0) {
				nodeName += "\nLABEL: "+srcLabel;
			}
			srcRoot.putAttr(XCSG.name, nodeName);
			
			srcLabel +=1;
		}else {
			r = srcIsoNodes.get(srcRoot);
			r.depth.add(0);
		}
		
		createIsoNodes(srcGraph, 1, mode, srcIsoNodes, srcCreatedIso, srcLabel, r, rootOut);
		

		Node binRoot = binGraph.eval().nodes().tagged(XCSG.controlFlowRoot).one();
		AtlasSet<Edge> binRootOut = binRoot.out().tagged("bin_induced_edge");
		isoNode binR = new isoNode(binRoot, binLabel);
		binR.depth.add(0);
		
		if (!binIsoNodes.containsKey(binRoot)) {
			binIsoNodes.put(binRoot, binR);
			binCreatedIso.add(binR);
			
			nodeName = binRoot.getAttr(XCSG.name).toString();
			if (mode == 0) {
				nodeName += "\nLABEL: "+binLabel;
			}
			binRoot.putAttr(XCSG.name, nodeName);
			
			binLabel +=1;
		}else {
			binR = binIsoNodes.get(binRoot);
			binR.depth.add(0);
		}
		
		createIsoNodes(binGraph, 0, mode, binIsoNodes, binCreatedIso, binLabel, binR, binRootOut);
		AtlasSet<Node> binNodes = binGraph.eval().nodes().tagged("bin_node");

		if (functionName.contains("getpath")) {
			System.out.println("here");
		}
		

		Map<isoNode,isoNode> reTaggedLoops = new HashMap<isoNode,isoNode>();
		boolean breakFlag = false; 

			//Check to make sure loop headers are properly tagged
			for (int i = 0; i < srcLoops.size() && i < binLoops.size(); i++) {
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
				
				ArrayList<String> sAttr = new ArrayList<String>();
				for (Node s : srcChildren) {
					sAttr.add(s.getAttr("child_id").toString());
				}
				
				ArrayList<String> bAttr = new ArrayList<String>();
				for (Node s : binChildren) {
					bAttr.add(s.getAttr("child_id").toString());
				}
				
				boolean checking = bAttr.containsAll(sAttr);
				if (!checking) {
					
					ArrayList<isoNode> bNodes = new ArrayList<isoNode>();
					for (Node b : binChildren) {
						isoNode gettingIso = binIsoNodes.get(b);
						bNodes.add(gettingIso);
					}
					bAttr.clear();
					
					for (isoNode currentIso : bNodes) {
						ArrayList<Node> gcNodes = new ArrayList<Node>();
						for (Node g : currentIso.loopChildren) {
							gcNodes.add(g);
							bAttr.add(g.getAttr("child_id").toString());
						}
						
						for (Node c : gcNodes) {
							String gcName = c.getAttr(XCSG.name).toString();
							
							if (bAttr.containsAll(sAttr) && gcName.contains(bin.graphNode.getAttr(XCSG.name).toString()) && !reTaggedLoops.containsKey(currentIso)) {
								int temp = currentIso.label;
								isoNode oldHeader = binIsoNodes.get(c);
								int parent = oldHeader.label;
								currentIso.label = parent;
								oldHeader.label = temp;
								
//								if (!reTaggedLoops.containsKey(currentIso)) {
									loopRetagging(binCreatedIso, currentIso, oldHeader, binNodes, binIsoNodes);
									breakFlag = true;
									
									reTaggedLoops.put(currentIso, oldHeader);
									break;
//								}
							}
						}
					}
				}
			}
			if (breakFlag) {
				for (int x = 0; x < binCreatedIso.size(); x++) {
					for (int y = x + 1; y < binCreatedIso.size(); y++) {
						isoNode checkingB = binCreatedIso.get(x);
						isoNode nextNode = binCreatedIso.get(y);
						
						if (checkingB.label > nextNode.label) {
							binCreatedIso.set(y, checkingB);
							binCreatedIso.set(x, nextNode);
						}
					}
				}
				
				for (int x = 0; x < srcCreatedIso.size(); x++) {
					for (int y = x + 1; y < srcCreatedIso.size(); y++) {
						isoNode checkingB = srcCreatedIso.get(x);
						isoNode nextNode = srcCreatedIso.get(y);
						
						if (checkingB.label > nextNode.label) {
							srcCreatedIso.set(y, checkingB);
							srcCreatedIso.set(x, nextNode);
						}
					}
				}
			}
			
		
		
		int sFail = srcCreatedIso.get(0).label;
		int bFail = binCreatedIso.get(0).label;
		Node sNode = srcCreatedIso.get(0).graphNode;
		Node bNode = binCreatedIso.get(0).graphNode;
		
		long isoCount = 0; 
		for (int i = 0; i < srcCreatedIso.size() && i < binCreatedIso.size(); i++) {
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
				sFail = s.label;
				bFail = b.label;
				sNode = s.graphNode;
				bNode = b.graphNode;
				break;
			}
		}
		
		boolean result;
		result = false;
		if (isoCount == srcGraph.eval().nodes().tagged("src_node").size()) {
			result = true;
		}
		isoNodeResult g = new isoNodeResult(result, srcGraph.eval().nodes().size(), binGraph.eval().nodes().size(), message, sFail, bFail, sNode, bNode);
		return g;
	}
	
	public static void colorGraphs(String functionName) {
		
		isoNodeResult t = isomorphismChecker(functionName, 0);
		isoNodeResult r = isomorphismChecker(functionName, 1);
		Node srcForward = t.srcFailNode;
		Node srcReverse = r.srcFailNode;
		
		String srcFName = srcForward.getAttr(XCSG.name).toString().split("LABEL:")[0];
		srcFName = srcFName.replaceAll("\\n", "");
		String srcRName = srcReverse.getAttr(XCSG.name).toString().split("LABEL:")[0];
		srcRName = srcRName.replaceAll("\\n", "");
		
		Q srcTransformed = srcTransformedGraph(functionName.substring(4));
		DAGTransform d = new DAGTransform();
		Q srcDAG = d.transform(srcTransformed);
		Node sFwd = null;
		Node sRev = null;
		
		for (Node n : srcDAG.eval().nodes()) {
			String nName = n.getAttr(XCSG.name).toString();
			if (nName.contains(srcFName)) {
				sFwd = n;
			}
			
			if (nName.contains(srcRName)) {
				sRev = n;
			}
		}
		
		Q fwdQ = Common.toQ(sFwd);
		Q revQ = Common.toQ(sRev);
		Markup m = new Markup();
		AtlasSet<Node> errorNodes = srcDAG.between(fwdQ, revQ).selectEdge(XCSG.ControlFlow_Edge).eval().nodes();
		
//		System.out.println("error size: "+errorNodes.size());
		m.setNode(srcTransformed.between(fwdQ, revQ), MarkupProperty.NODE_BACKGROUND_COLOR, java.awt.Color.YELLOW);
		m.setNode(fwdQ, MarkupProperty.NODE_BACKGROUND_COLOR, java.awt.Color.GREEN);
		m.setNode(revQ, MarkupProperty.NODE_BACKGROUND_COLOR, java.awt.Color.RED);
		
		if (sFwd.getAttr(XCSG.name).toString().equals(sRev.getAttr(XCSG.name).toString())) {
			m.setNode(revQ, MarkupProperty.NODE_BACKGROUND_COLOR, java.awt.Color.CYAN);
		}

		
		DisplayUtil.displayGraph(m, srcTransformed.eval());
	}
	
	
	public static void checkAllIso() throws IOException {
		String isoPath = "/Users/RyanGoluch/Desktop/Masters_Work/final_result_testing/iso_results_mips_vs_ppc_xinu.csv";
		File isoFile = new File(isoPath);
		BufferedWriter isoWriter = new BufferedWriter(new FileWriter(isoFile));
		isoWriter.write("Function Name, Mips Iso Result, PPC Iso Result, Src Node Count, Mips Bin Node Count, PPC Bin Node Count, Error, Arch Specific Insr Count, Iso Category\n");
		
		int trueCount = 0; 
		int falseCount = 0;
		int linearCount = 0;
		int errorCount = 0;
		int srcCondition = 0;
		int sltNodeCounter = 0; 
		
		Q functions = Query.universe().nodesTaggedWithAll(XCSG.Function, "ppc_xinu");
		System.out.println("function size: "+functions.eval().nodes().size());
		for (Node function : functions.eval().nodes()) {
			
			String fName = function.getAttr(XCSG.name).toString();
			System.out.println("name: "+fName);

			if(fName.contains("setupStack") || fName.contains("test") || fName.contains("lexan") 
					|| fName.contains("enqueue") || fName.contains("insert") || fName.contains("dispatch") || fName.contains("_doprnt") 
					|| fName.contains("rwhod") || fName.matches("ppc_netin")
					|| fName.contains("rwhoind"))  {
//				|| fName.contains("x_rls") || fName.contains("x_mount") || fName.contains("rwhoind") || fName.contains("netin")
//				|| fName.contains("login")
				
				continue;
			}
			
			isoNodeResult result = isomorphismChecker(fName,0);
			isoNodeResult revResult = isomorphismChecker(fName,1);
			
			if (result.error.contains("Binary only function:")) {
				System.out.println("bin only: "+fName);
				continue;
			}
			
			Q binGraph = bcfg(fName);
			for (Node n : binGraph.eval().nodes()) {
				String nodeName = n.getAttr(XCSG.name).toString();
//				if (result.binSize != 0 && result.error != null) {
					if (nodeName.contains("slti") || nodeName.contains("sltiu") || nodeName.contains("slt") || nodeName.contains("sltu") || nodeName.contains("cmp")) {
						result.error += "Architecture Specific Instr";
						sltNodeCounter +=1;
						break;
					}
//				}
			}
			
			
//			if (result.error == "") {
				if (result.result == true || result.error.contains("Linear src function : Linear binary")) {
					trueCount +=1;
//					if (result.error == "") {
						isoWriter.write(fName + "," + result.result + "," + result.srcSize + "," + result.binSize + ", , , , , , ," + result.error + "\n");
						isoWriter.flush();
//					}else 
						if (result.error.contains("Linear src function : Linear binary") && result.result != true){
//						System.out.println(fName);
						linearCount +=1;
					}
					
					
//					Q src = srcTransformedGraph(fName.substring(6));
//					Q bin = binTransformedGraph(fName);
//					SaveUtil.saveGraph(new File(graphPath+"/true_graphs/"+"src_"+fName.substring(4)+"_cfg.png"), src.eval());
//					SaveUtil.saveGraph(new File(graphPath+"/true_graphs/"+"bin_"+fName+"_cfg.png"), bin.eval());
					
				}else if (result.result == false){
//					falseCount +=1;
					
					long srcFailSize = 0;
					long binFailSize = 0;
					
					if (result.srcFailNode != null && revResult.srcFailNode != null && result.binFailNode != null && revResult.binFailNode != null) {
						Q srcFwdFail = Common.toQ(result.srcFailNode);
						Q srcRevFail = Common.toQ(revResult.srcFailNode);
						srcFailSize = srcTransformedGraph(fName.substring(4)).between(srcFwdFail, srcRevFail).eval().nodes().size();
						
						Q binFwdFail = Common.toQ(result.binFailNode);
						Q binRevFail = Common.toQ(revResult.binFailNode);
						binFailSize = binTransformedGraph(fName).between(binFwdFail, binRevFail).eval().nodes().size();
					}
					
					if (result.error == "") {
						falseCount +=1;
						isoWriter.write(fName + "," + result.result + "," + result.srcSize + "," + result.binSize + "," + srcFailSize + "," + binFailSize + "," + 
								result.srcFailLabel + "," + revResult.srcFailLabel + "," + result.binFailLabel + "," + revResult.binFailLabel + "," + result.error +"\n");
						isoWriter.flush();
					}
					else if (result.error.contains("Architecture Specific Instr")) {
						isoWriter.write(fName + "," + result.result + "," + result.srcSize + "," + result.binSize + "," + srcFailSize + "," + binFailSize + "," + 
								result.srcFailLabel + "," + revResult.srcFailLabel + "," + result.binFailLabel + "," + revResult.binFailLabel + "," + result.error +"\n");
						isoWriter.flush();
					}
					else if(result.error.contains("Src Condition : Linear Binary")) {
						srcCondition +=1;
						isoWriter.write(fName + "," + result.result + "," + result.srcSize + "," + result.binSize + "," + srcFailSize + "," + binFailSize + "," + 
								result.srcFailLabel + "," + revResult.srcFailLabel + "," + result.binFailLabel + "," + revResult.binFailLabel + "," + result.error +"\n");
						isoWriter.flush();
					}
					else if (!result.error.contains("Architecture Specific Instr")){
						errorCount +=1;
						isoWriter.write(fName + "," + result.result + "," + result.srcSize + "," + result.binSize + "," + srcFailSize + "," + binFailSize + "," + 
								result.srcFailLabel + "," + revResult.srcFailLabel + "," + result.binFailLabel + "," + revResult.binFailLabel + "," + result.error +"\n");
						isoWriter.flush();
					}
					
//					if (result.error == "") {
//						Q src = srcTransformedGraph(fName.substring(6));
//						Q bin = binTransformedGraph(fName);
//						SaveUtil.saveGraph(new File(graphPath+"/false_graphs/"+"src_"+fName.substring(4)+"_cfg.png"), src.eval());
//						SaveUtil.saveGraph(new File(graphPath+"/false_graphs/"+"bin_"+fName+"_cfg.png"), bin.eval());
//					}else {
//						Q src = srcTransformedGraph(fName.substring(6));
//						Q bin = binTransformedGraph(fName);
//						SaveUtil.saveGraph(new File(graphPath+"/error_graphs/"+"src_"+fName.substring(4)+"_cfg.png"), src.eval());
//						SaveUtil.saveGraph(new File(graphPath+"/error_graphs/"+"bin_"+fName+"_cfg.png"), bin.eval());
//					}
				}
				
				
//			} else {
//				if (result.error.contains("Empty binary") || result.error.contains("Single node src") || result.error.contains("Linear Binary")) {
//					isoWriter.write(fName + "," + result.result + "," + result.srcSize + "," + result.binSize + ", , , , , , ," + result.error + "\n");
//					isoWriter.flush();
//			}
//			else {
//				
//				Q srcFwdFail = Common.toQ(result.srcFailNode);
//				Q srcRevFail = Common.toQ(revResult.srcFailNode);
//				long srcFailSize = srcTransformedGraph(fName.substring(4)).between(srcFwdFail, srcRevFail).eval().nodes().size();
//				
//				Q binFwdFail = Common.toQ(result.binFailNode);
//				Q binRevFail = Common.toQ(revResult.binFailNode);
//				long binFailSize = binTransformedGraph(fName).between(binFwdFail, binRevFail).eval().nodes().size();
//				
//				isoWriter.write(fName + "," + result.result + "," + result.srcSize + "," + result.binSize + "," + srcFailSize + "," + binFailSize + "," + 
//								result.srcFailLabel + "," + revResult.srcFailLabel + "," + result.binFailLabel + "," + revResult.binFailLabel + "," + result.error +"\n");
//				isoWriter.flush();
//				
//				if (result.binSize != 0 && result.error.equals("Node count mismatch") && result.binSize != result.srcSize) {
//					errorCount +=1;
//					isoWriter.write(fName + "," + result.result + "," + result.srcSize + "," + result.binSize + "," + result.error + "\n");
//					isoWriter.flush();
//				}
//				else if (!result.error.contains("Binary only function: ") && !result.error.contains("SLTI Function") && result.binSize != 0) {
//					errorCount +=1;
//					isoWriter.write(fName + "," + result.result + "," + result.srcSize + "," + result.binSize + "," + result.error + "\n");
//					isoWriter.flush();
//				}
//			}
		}
		
		isoWriter.write("\n");
		isoWriter.write("True Count, False Count, Linear Count, ErrorCount, Src Condition : Linear Binary, Architecture Specific Instr\n");
		isoWriter.write(trueCount +","+falseCount+","+linearCount+","+errorCount+","+srcCondition+","+sltNodeCounter);
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
				else if (result.error.contains("SLT Function")) {
					sltCount +=1;
					isoWriter.write(fName + "," + result.result + "," + result.srcSize + "," + result.binSize + "," + result.error + "," + sltNodeCounter + "\n");
					isoWriter.flush();
				}
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
	
	public static void createIsoNodes(Q graph, int flag, int mode, Map<Node, isoNode> isoNodes, ArrayList<isoNode> createdIso, int label, isoNode r, AtlasSet<Edge> rootOut) {
		
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
		ArrayList<Node> sortedNodes = new ArrayList<Node>();
		for (Node n : srcNodes) {
			sortedNodes.add(n);
		}
		
		if (nodeTag.equals("src_node")) {
			
			for (int i = 0; i < sortedNodes.size(); i++) {
				for (int j = i+1; j < sortedNodes.size(); j++) {
					Node x = sortedNodes.get(i);
					Node y = sortedNodes.get(j);
				
					long temp;
					long current;
					if (x.taggedWith(XCSG.controlFlowExitPoint) && mode == 0 && x.hasAttr("line_number")) {
//						!x.taggedWith("reversed_graph")
						temp = Long.parseLong(x.getAttr("line_number").toString(), 10);
					} else if (x.taggedWith(XCSG.controlFlowRoot) && mode != 0) {
//						x.taggedWith("reversed_graph")
						temp = Long.parseLong(x.getAttr("line_number").toString(), 10);
					}
					else {
						temp = getCSourceLineNumber(x);
					}
					
					if (y.taggedWith(XCSG.controlFlowExitPoint) && mode == 0 && y.hasAttr("line_number")) {
//						!y.taggedWith("reversed_graph")
						current = Long.parseLong(y.getAttr("line_number").toString(), 10);
					}else if (y.taggedWith(XCSG.controlFlowRoot) && mode != 0) {
//						y.taggedWith("reversed_graph")
						current = Long.parseLong(y.getAttr("line_number").toString(), 10);
					}else {
						current = getCSourceLineNumber(y);
					}
					
					if (temp > current && !x.taggedWith("case_node") || (x.taggedWith("sc_end") && temp == current)) {
						sortedNodes.set(i,y);
						sortedNodes.set(j, x);
					}
				}
			}
		}else {
			
			for (int i = 0; i < sortedNodes.size(); i++) {
				for (int j = i+1; j < sortedNodes.size(); j++) {
					Node x = sortedNodes.get(i);
					Node y = sortedNodes.get(j);
					
					int temp = (int) x.getAttr("line_number");
					int current = (int) y.getAttr("line_number");
					if (temp > current) {
						sortedNodes.set(i,y);
						sortedNodes.set(j, x);
					}
				}
			}
		}
		
		
		for (Node n : sortedNodes) {
			if (!isoNodes.containsKey(n)) {
				isoNode x = new isoNode(n, label);
				
				String nodeName = n.getAttr(XCSG.name).toString();
				if (mode == 0) {
					nodeName += "\nLABEL: "+label;
				}
				n.putAttr(XCSG.name, nodeName);
				
				label +=1;
				isoNodes.put(n, x);
				createdIso.add(x);
			}else if (n.taggedWith(XCSG.ControlFlowLoopCondition) && !isoNodes.containsKey(n)){
				isoNode loopHeader = isoNodes.get(n);
				loopHeader.structure = XCSG.ControlFlowLoopCondition;
				createdIso.add(loopHeader);
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
	
	private static class isoNodeResult{
		private boolean result;
		private long srcSize; 
		private long binSize;
		private String error; 
		private int srcFailLabel; 
		private int binFailLabel;
		private Node srcFailNode;
		private Node binFailNode;
//		private long failSize; 
		
		public isoNodeResult(boolean r, long s, long b, String e, int sLabel, int bLabel, Node sNode, Node bNode) {
			this.result = r;
			this.binSize = b;
			this.srcSize = s;
			this.error = e;
			this.binFailLabel = bLabel;
			this.srcFailLabel = sLabel;
			this.binFailNode = bNode;
			this.srcFailNode = sNode;
//			this.failSize = f; 
		}
	
	}
}
