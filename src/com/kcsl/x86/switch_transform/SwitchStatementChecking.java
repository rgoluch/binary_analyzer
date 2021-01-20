package com.kcsl.x86.switch_transform;

import static com.kcsl.x86.Importer.my_cfg;
import static com.kcsl.x86.Importer.my_function;

import java.io.BufferedWriter;
import java.io.File;
import java.io.FileWriter;
import java.io.IOException;
import java.util.ArrayList;
import java.util.HashMap;
import java.util.Map;

import com.ensoftcorp.atlas.core.db.graph.Edge;
import com.ensoftcorp.atlas.core.db.graph.Graph;
import com.ensoftcorp.atlas.core.db.graph.Node;
import com.ensoftcorp.atlas.core.db.set.AtlasSet;
import com.ensoftcorp.atlas.core.index.common.SourceCorrespondence;
import com.ensoftcorp.atlas.core.query.Q;
import com.ensoftcorp.atlas.core.query.Query;
import com.ensoftcorp.atlas.core.script.Common;
import com.ensoftcorp.atlas.core.xcsg.XCSG;

public class SwitchStatementChecking {

	
	public static ArrayList<String> switchChecker() {
		
		ArrayList<String> switchFunctions = new ArrayList<String>();
		
		Q functions = Query.universe().nodesTaggedWithAll(XCSG.Function, "binary_function");
		int switchCount = 0;
		System.out.println("Switch Statements: ");
		for (Node f : functions.eval().nodes()) {
			String functionName = f.getAttr(XCSG.name).toString();
			String srcName = functionName.substring(4);
			
			Q function = my_function(srcName);
			Q c = my_cfg(function);
			for (Node n : c.eval().nodes()) {
				if (n.taggedWith(XCSG.ControlFlowSwitchCondition)) {
//					System.out.println(srcName);
					switchCount++;
					switchFunctions.add(srcName);
				}
			}
		}
		
		System.out.println("Total number of switch functions: " + switchCount);
		return switchFunctions;
	}
	
	public static ArrayList<caseNode> caseSorter(ArrayList<caseNode> cases) {
		
//		String switchPath = "/Users/RyanGoluch/Desktop/Masters_Work/switch_checking/switch_order_checking.csv";
//		File switchFile = new File(switchPath);
//		BufferedWriter switchWriter = new BufferedWriter(new FileWriter(switchFile));
//		switchWriter.write("Function Name, # of Cases, Case Ordering\n");
		
			
//		ArrayList<String> functions = switchChecker();		
//		for (String s : functions) {
//			Q function = my_function(s);
//			Q c = my_cfg(function);
			
			ArrayList<caseNode> nodes = new ArrayList<caseNode>();
			
//			for (Node n : cases) {
//				if (n.taggedWith(XCSG.CaseLabel)) {
//					long l = getCSourceLineNumber(n);
//					caseNode x = new caseNode(n, l, 0, 0);
//					nodes.add(x);
//				}
//			}
			
			for (int i = 0; i < cases.size(); i++) {
				for (int j = i+1; j < cases.size(); j++) {
					caseNode x = cases.get(i);
					caseNode y = cases.get(j);
					long temp = cases.get(i).getLineNumber();
					long current = cases.get(j).getLineNumber();
					if (temp > current) {
						cases.set(i,y);
						cases.set(j, x);
					}
				}
			}
			
			for (caseNode c : cases) {
				System.out.println(c.getLineNumber());
			}
		return cases;
//		switchWriter.close();
		
	}
	
	public static Q switchTransform(String name) {
		
		//Get the original source CFG
		Q f = my_function(name);	
		Q c = my_cfg(f);
		
		//Set up for new function node for returned CFG
		Node functionNode = Graph.U.createNode();
		functionNode.putAttr(XCSG.name, "switch_transform_"+name);
		functionNode.tag(XCSG.Function);
		functionNode.tag("switch_graph");
		
		Map<Node,Node> recreatedNodes = new HashMap<Node,Node>();
		ArrayList<caseNode> caseNodes = new ArrayList<caseNode>();
		Map<Integer,Node> switchPredecessors = new HashMap<Integer,Node>();

		Node defNode = null;
		
		for (Edge e : c.eval().edges().tagged(XCSG.ControlFlow_Edge)) {
			if (e.to().taggedWith(XCSG.ControlFlowSwitchCondition)) {
				
				Node predecessor = e.from();
				Node recreatedCheck = recreatedNodes.get(predecessor);
				
				if (recreatedCheck == null) {
					Node tempPred = Graph.U.createNode();
					tempPred.putAttr(XCSG.name, predecessor.getAttr(XCSG.name).toString());
					tempPred.tag("switch_graph");
					tempPred.tag("switch_pred");
					tempPred.tag(XCSG.ControlFlow_Node);
					
					if (predecessor.taggedWith(XCSG.ControlFlowCondition)) {
						tempPred.tag(XCSG.ControlFlowCondition);
					}
					
					Edge e1 = Graph.U.createEdge(functionNode, tempPred);
					e1.tag(XCSG.Contains);
					recreatedNodes.put(predecessor, tempPred);
					switchPredecessors.put(predecessor.addressBits(), tempPred);
				}
				else {
					recreatedCheck.tag("switch_pred");
					switchPredecessors.put(predecessor.addressBits(), recreatedCheck);
				}
				
				Node switchNode = e.to();
				
				for(Edge defEdge : switchNode.out()) {
					if (defEdge.hasAttr(XCSG.conditionValue)) {
						if (defEdge.getAttr(XCSG.conditionValue).toString().contains("default")) {
							Node addedCheck = recreatedNodes.get(defEdge.to());
							
							if (addedCheck == null) {
								Node tempDef = Graph.U.createNode();
								tempDef.putAttr(XCSG.name, defEdge.to().getAttr(XCSG.name).toString());
								tempDef.tag("switch_graph");
								tempDef.tag("switch_def");
								tempDef.tag(XCSG.ControlFlow_Node);
								
								if (defEdge.to().taggedWith(XCSG.ControlFlowCondition)) {
									tempDef.tag(XCSG.ControlFlowCondition);
								}
								
								Edge e1 = Graph.U.createEdge(functionNode, tempDef);
								e1.tag(XCSG.Contains);
								recreatedNodes.put(defEdge.to(), tempDef);
								defNode = tempDef;
							}
							else {
								defNode = addedCheck;
								defNode.tag("switch_def");
							}
						}
					}
				}
			}
			else if (e.from().taggedWith(XCSG.CaseLabel) && !e.from().taggedWith(XCSG.DefaultCaseLabel)) {
//				Edge e3 = Graph.U.createEdge(functionNode, e.to());
//				e3.tag(XCSG.Contains);
				
				Node trueEval = e.to();
				Node recreatedCheck = recreatedNodes.get(trueEval);
				Node tempTrue = null;
					
				if (recreatedCheck == null) {
					tempTrue = Graph.U.createNode();
					tempTrue.putAttr(XCSG.name, trueEval.getAttr(XCSG.name).toString());
					tempTrue.tag("switch_graph");
					tempTrue.tag(XCSG.ControlFlow_Node);
					
					if (trueEval.taggedWith(XCSG.ControlFlowCondition)) {
						tempTrue.tag(XCSG.ControlFlowCondition);
					}
					
					Edge e1 = Graph.U.createEdge(functionNode, tempTrue);
					e1.tag(XCSG.Contains);
					recreatedNodes.put(trueEval, tempTrue);
				}
				else {
					tempTrue = recreatedCheck;
				}
				
				
				long l = getCSourceLineNumber(e.from());
				caseNode x = new caseNode(e.from(), l, tempTrue);
				
				caseNodes.add(x);
				continue;
			}
			else if (e.from().taggedWith(XCSG.DefaultCaseLabel)) {
				Node header = e.to();
				
				Node recreatedCheck = recreatedNodes.get(header);
				Node recreatedFromCheck = recreatedNodes.get(e.from());
				Node tempDefault = null;
				Node tempHeader = null;
				
				if (recreatedFromCheck == null) {
					tempDefault = Graph.U.createNode();
					
					tempDefault.putAttr(XCSG.name, e.from().getAttr(XCSG.name).toString());
					tempDefault.tag("switch_graph");
					tempDefault.tag("switch_def");
					tempDefault.tag(XCSG.ControlFlow_Node);
					
					Edge e1 = Graph.U.createEdge(functionNode, tempDefault);
					e1.tag(XCSG.Contains);
					defNode = tempDefault;
					recreatedNodes.put(e.from(), tempDefault);
				}
				else {
					tempDefault = recreatedFromCheck;
					defNode = tempDefault;
					defNode.tag("switch_def");
				}
				
				if (recreatedCheck == null) {
					tempHeader = Graph.U.createNode();
					
					tempHeader.putAttr(XCSG.name, header.getAttr(XCSG.name).toString());
					tempHeader.tag("switch_graph");
					tempHeader.tag(XCSG.ControlFlow_Node);
					
					Edge e1 = Graph.U.createEdge(functionNode, tempHeader);
					e1.tag(XCSG.Contains);
					
					if (header.taggedWith(XCSG.ControlFlowCondition)) {
						tempHeader.tag(XCSG.ControlFlowCondition);
					}
					if (header.taggedWith(XCSG.controlFlowExitPoint)) {
						tempHeader.tag(XCSG.controlFlowExitPoint);
					}
					recreatedNodes.put(header, tempHeader);
				}
				else {
					tempHeader = recreatedCheck;
				}
				
				Edge defaultEdge = Graph.U.createEdge(tempDefault, tempHeader);
				defaultEdge.tag(XCSG.ControlFlow_Edge);
				defaultEdge.tag("switch_edge");
			}
			else if (e.to().taggedWith(XCSG.DefaultCaseLabel) && !e.from().taggedWith(XCSG.ControlFlowSwitchCondition)) {
				Node header = e.to();
				
				Node recreatedCheck = recreatedNodes.get(header);
				Node recreatedFromCheck = recreatedNodes.get(e.from());
				Node tempDefault = null;
				Node tempHeader = null;
				
				if (recreatedFromCheck == null) {
					tempDefault = Graph.U.createNode();
					
					tempDefault.putAttr(XCSG.name, e.from().getAttr(XCSG.name).toString());
					tempDefault.tag("switch_graph");
					tempDefault.tag(XCSG.ControlFlow_Node);
					
					Edge e1 = Graph.U.createEdge(functionNode, tempDefault);
					e1.tag(XCSG.Contains);
					
					if (e.from().taggedWith(XCSG.ControlFlowCondition)) {
						tempDefault.tag(XCSG.ControlFlowCondition);
					}
					if (e.from().taggedWith(XCSG.controlFlowExitPoint)) {
						tempDefault.tag(XCSG.controlFlowExitPoint);
					}
					
					recreatedNodes.put(e.from(), tempDefault);
				}
				else {
					tempDefault = recreatedFromCheck;
				}
				
				if (recreatedCheck == null) {
					tempHeader = Graph.U.createNode();
					
					tempHeader.putAttr(XCSG.name, header.getAttr(XCSG.name).toString());
					tempHeader.tag("switch_graph");
					tempHeader.tag("switch_def");
					tempHeader.tag(XCSG.ControlFlow_Node);
					
					Edge e1 = Graph.U.createEdge(functionNode, tempHeader);
					e1.tag(XCSG.Contains);
					
					defNode = tempHeader;
					recreatedNodes.put(header, tempHeader);
				}
				else {
					tempHeader = recreatedCheck;
					defNode = tempHeader;
					defNode.tag("switch_def");
				}
				
				Edge defaultEdge = Graph.U.createEdge(tempDefault, tempHeader);
				defaultEdge.tag(XCSG.ControlFlow_Edge);
				defaultEdge.tag("switch_edge");
			}
			else if (!e.from().taggedWith(XCSG.CaseLabel) && !e.from().taggedWith(XCSG.ControlFlowSwitchCondition) && !e.to().taggedWith(XCSG.CaseLabel)) {
				Node from = e.from();
				Node to = e.to();
				
				Node tempFrom = Graph.U.createNode();
				Node tempTo = Graph.U.createNode();
				
				tempFrom.putAttr(XCSG.name, from.getAttr(XCSG.name).toString());
				tempFrom.tag("switch_graph");
				tempFrom.tag(XCSG.ControlFlow_Node);
				tempTo.putAttr(XCSG.name, to.getAttr(XCSG.name).toString());
				tempTo.tag("switch_graph");
				tempTo.tag(XCSG.ControlFlow_Node);
				
				if (from.taggedWith(XCSG.ControlFlowCondition)) {
					tempFrom.tag(XCSG.ControlFlowCondition);
				}
				if (from.taggedWith(XCSG.controlFlowExitPoint)) {
					tempFrom.tag(XCSG.controlFlowExitPoint);
				}
				if (to.taggedWith(XCSG.ControlFlowCondition)) {
					tempTo.tag(XCSG.ControlFlowCondition);
				}
				if (to.taggedWith(XCSG.controlFlowExitPoint)) {
					tempTo.tag(XCSG.controlFlowExitPoint);
				}
				
				Node checkFrom = recreatedNodes.get(from);
				Node checkTo = recreatedNodes.get(to);
				Edge tempEdge = null;

				if (checkFrom == null && checkTo == null) {
					Edge e1 = Graph.U.createEdge(functionNode, tempFrom);
					e1.tag(XCSG.Contains);
					
					Edge e2 = Graph.U.createEdge(functionNode, tempTo);
					e2.tag(XCSG.Contains);
					
					tempEdge = Graph.U.createEdge(tempFrom, tempTo);
					tempEdge.tag(XCSG.ControlFlow_Edge);
					tempEdge.tag("switch_edge");
					
					recreatedNodes.put(from, tempFrom);
					recreatedNodes.put(to, tempTo);
				}
				
				if (checkFrom != null && checkTo == null) {
					Edge e2 = Graph.U.createEdge(functionNode, tempTo);
					e2.tag(XCSG.Contains);
					
					tempEdge = Graph.U.createEdge(checkFrom, tempTo);
					tempEdge.tag(XCSG.ControlFlow_Edge);
					tempEdge.tag("switch_edge");
					
					recreatedNodes.put(to, tempTo);
				}
				
				if (checkFrom == null && checkTo != null) {
					Edge e2 = Graph.U.createEdge(functionNode, tempFrom);
					e2.tag(XCSG.Contains);
					
					tempEdge = Graph.U.createEdge(tempFrom, checkTo);
					tempEdge.tag(XCSG.ControlFlow_Edge);
					tempEdge.tag("switch_edge");
					
					recreatedNodes.put(from, tempFrom);
				}
				
				
				if (e.taggedWith(XCSG.ControlFlowBackEdge)) {
					tempEdge.tag(XCSG.ControlFlowBackEdge);
				}
				
				if (e.hasAttr(XCSG.conditionValue)) {
					if (e.getAttr(XCSG.conditionValue).toString().contains("true")) {
						tempEdge.putAttr(XCSG.conditionValue, "true");
					}else {
						tempEdge.putAttr(XCSG.conditionValue, "false");
					}
				}
			}
		}
		
		ArrayList<caseNode> sortedCases = caseSorter(caseNodes);
		ArrayList<Node> bstNodes = bstCaseNodes(sortedCases, functionNode, defNode);
		
		Node firstCase = bstNodes.get(0);
		
		for (Node n : switchPredecessors.values()) {
			Edge predEdge = Graph.U.createEdge(n, firstCase);
			predEdge.tag(XCSG.ControlFlow_Edge);
			predEdge.tag("switch_edge");
		}
		
//		for (int i = 0; i < trueNodes.size() - 1; i++) {
//			Edge continuation = Graph.U.createEdge(trueNodes.get(i), trueNodes.get(i+1));
//			continuation.tag(XCSG.ControlFlow_Edge);
//			continuation.tag("switch_edge");
//		}
		
		
		Q x = my_function(functionNode.getAttr(XCSG.name).toString());
		Q switch_cfg = my_cfg(x);
		return switch_cfg.nodes("bst_node");
//				.induce(Query.universe().edges("switch_edge"));
	}
	
	
	
	public static ArrayList<Node> bstCaseNodes(ArrayList<caseNode> nodes, Node functionNode, Node finalDest) {
		ArrayList<Node> bst = new ArrayList<Node>();
		
		int l = 0;
		int r = nodes.size() - 1;
		int mid = (l + r) / 2;
		int bstIndex = 0;
		
		Map<Node, Node> casesAdded = new HashMap<Node, Node>();
		
		int sizeCheck; 
		boolean sizeFlag = false;
		boolean midpointToggle = false;
		
		if (nodes.size() < 4) {
			sizeCheck = nodes.size();
		}
		else {
			sizeCheck = nodes.size()+1;
			sizeFlag = true;
		}
		
//		ArrayList<caseNode> treeNodes = new ArrayList<caseNode>();
//		for (caseNode t : nodes) {
//			Node caseCreate = Graph.U.createNode();
//			
//			//Create the case condition
//			caseCreate.putAttr(XCSG.name, t.getOriginalNode().getAttr(XCSG.name).toString());
//			caseCreate.tag(XCSG.ControlFlowCondition);
//			caseCreate.tag("switch_graph");
//			caseCreate.tag("bst_node");
//			
//			//Add to return graph
//			Edge containerEdge = Graph.U.createEdge(functionNode, caseCreate);
//			containerEdge.tag(XCSG.Contains);
//			
//			treeNodes.add(caseCreate);
//		}
		
//		boolean checkFlag = false;
//		
//		if (nodes.size() >= 4) {
//			Node checkPoint = Graph.U.createNode();
//			checkPoint.putAttr(XCSG.name, "direction checkpoint");
//			checkPoint.tag(XCSG.ControlFlowCondition);
//			checkPoint.tag("switch_graph");
//			checkPoint.tag("bst_node");
//			checkPoint.tag("check");
//			
////			Edge checkPointEdge = Graph.U.createEdge(functionNode, checkPoint);
////			checkPointEdge.tag(XCSG.Contains);
//			
//			int toMidPoint = (l + (mid-1)) / 2;
//			Node toNode = nodes.get(toMidPoint).getOriginalNode();
//			
//			caseNode c = new caseNode(checkPoint, 0, toNode);
//			nodes.add(c);
//			
//			int swapMidPoint = (mid + 1 + r) / 2;
//			for (int i = swapMidPoint; i < nodes.size()-1; i++) {
//				caseNode temp = nodes.get(i);
//				caseNode end = nodes.get(nodes.size()-1);
//				nodes.set(i, end);
//				nodes.set(nodes.size()-1, temp);
//			}
////			checkFlag = true;
//		}
//		bstNode tree = bstBuilder(nodes, 0, nodes.size()-1);
//		
//		Node checkPoint = Graph.U.createNode();
//		checkPoint.putAttr(XCSG.name, "direction checkpoint");
//		checkPoint.tag(XCSG.ControlFlowCondition);
//		checkPoint.tag("switch_graph");
//		checkPoint.tag("bst_node");
//		checkPoint.tag("check");
//		
////		Edge checkPointEdge = Graph.U.createEdge(functionNode, checkPoint);
////		checkPointEdge.tag(XCSG.Contains);
//				
//		bstNode c = new bstNode(checkPoint);
//		c.leftChild = tree.leftChild;
//		c.rightChild = tree.rightChild;
//		tree.leftChild = c;
//		tree.rightChild = new bstNode(nodes.get(mid).getToNode());

		while(l <= r) {
			mid = (l + r)/2;
			Node current = nodes.get(mid).getOriginalNode();
			Node caseCreate = Graph.U.createNode();
			
			//Create the case condition
			caseCreate.putAttr(XCSG.name, current.getAttr(XCSG.name).toString());
			caseCreate.tag(XCSG.ControlFlowCondition);
			caseCreate.tag("switch_graph");
			caseCreate.tag("bst_node");
			
			r = mid-1; 
			
			//Add to array for size check
			if (casesAdded.get(current) == null) {
				bst.add(caseCreate);
				casesAdded.put(current, caseCreate);
				
				//Add to return graph
				Edge containerEdge = Graph.U.createEdge(functionNode, caseCreate);
				containerEdge.tag(XCSG.Contains);
				
				//Set true destination
				Node trueDest = nodes.get(mid).getToNode();
				trueDest.tag("bst_node");
//				trueDests.add(trueDest);
				
				Edge trueEdge = Graph.U.createEdge(caseCreate, trueDest);
				trueEdge.tag("bst_edge");
				trueEdge.tag("switch_edge");
				trueEdge.putAttr(XCSG.conditionValue, true);
				trueEdge.tag(XCSG.ControlFlow_Edge);
				
//				if (bstIndex == 3 || bstIndex == 4) {
//					Edge falseEdge = Graph.U.createEdge(bst.get(1), caseCreate);
//					falseEdge.putAttr(XCSG.conditionValue, false);
//					falseEdge.tag(XCSG.ControlFlow_Edge);
//					falseEdge.tag("bst_edge");
//					falseEdge.tag("switch_edge");
//				}
//				else 
					if (bstIndex != 0) {
					Edge falseEdge = Graph.U.createEdge(bst.get(bstIndex - 1), caseCreate);
					falseEdge.putAttr(XCSG.conditionValue, false);
					falseEdge.tag(XCSG.ControlFlow_Edge);
					falseEdge.tag("bst_edge");
					falseEdge.tag("switch_edge");
				}
//				else if (bstIndex == 1 && sizeFlag){
//					Node checkPoint = Graph.U.createNode();
//					checkPoint.putAttr(XCSG.name, "direction checkpoint");
//					checkPoint.tag(XCSG.ControlFlowCondition);
//					checkPoint.tag("switch_graph");
//					checkPoint.tag("bst_node");
//					
//					Edge checkPointEdge = Graph.U.createEdge(functionNode, checkPoint);
//					checkPointEdge.tag(XCSG.Contains);
//					
//					Edge falseEdge = Graph.U.createEdge(bst.get(bstIndex-1), checkPoint);
//					falseEdge.putAttr(XCSG.conditionValue, false);
//					falseEdge.tag(XCSG.ControlFlow_Edge);
//					falseEdge.tag("bst_edge");
//					falseEdge.tag("switch_edge");
//					
//					bst.add(checkPoint);
//					sizeFlag = false;
//					bstIndex++;
//				}
					bstIndex++;
			}
			
			//Get new mid point
//			if (!midpointToggle) {
//				int toggle_r = mid-1;
//				mid = (l+toggle_r) / 2; 
//				midpointToggle = true;
//			}
//			else {
//				l = mid+1;
//				mid = (toggle_l+r)/2;
//				midpointToggle = false;
//			}
		}
		
		l = 0;
		r = nodes.size() - 1;
		mid = (l + r) / 2;
//		l = mid+1;
		
		while(l <= r) {
			mid = (l + r)/2;
			Node current = nodes.get(mid).getOriginalNode();
			Node caseCreate = Graph.U.createNode();
			
			//Create the case condition
			caseCreate.putAttr(XCSG.name, current.getAttr(XCSG.name).toString());
			caseCreate.tag(XCSG.ControlFlowCondition);
			caseCreate.tag("switch_graph");
			caseCreate.tag("bst_node");
			
			l = mid+1; 
			
			//Add to array for size check
			if (casesAdded.get(current) == null) {
				bst.add(caseCreate);
				casesAdded.put(current, caseCreate);
				
				//Add to return graph
				Edge containerEdge = Graph.U.createEdge(functionNode, caseCreate);
				containerEdge.tag(XCSG.Contains);
				
				//Set true destination
				Node trueDest = nodes.get(mid).getToNode();
				trueDest.tag("bst_node");
//				trueDests.add(trueDest);
				
				Edge trueEdge = Graph.U.createEdge(caseCreate, trueDest);
				trueEdge.tag("bst_edge");
				trueEdge.tag("switch_edge");
				trueEdge.putAttr(XCSG.conditionValue, true);
				trueEdge.tag(XCSG.ControlFlow_Edge);
				
//				if (bstIndex == 3 || bstIndex == 4) {
//					Edge falseEdge = Graph.U.createEdge(bst.get(1), caseCreate);
//					falseEdge.putAttr(XCSG.conditionValue, false);
//					falseEdge.tag(XCSG.ControlFlow_Edge);
//					falseEdge.tag("bst_edge");
//					falseEdge.tag("switch_edge");
//				}
//				else 
					if (bstIndex != 0) {
					Edge falseEdge = Graph.U.createEdge(bst.get(bstIndex - 1), caseCreate);
					falseEdge.putAttr(XCSG.conditionValue, false);
					falseEdge.tag(XCSG.ControlFlow_Edge);
					falseEdge.tag("bst_edge");
					falseEdge.tag("switch_edge");
				}
//				else if (bstIndex == 1 && sizeFlag){
//					Node checkPoint = Graph.U.createNode();
//					checkPoint.putAttr(XCSG.name, "direction checkpoint");
//					checkPoint.tag(XCSG.ControlFlowCondition);
//					checkPoint.tag("switch_graph");
//					checkPoint.tag("bst_node");
//					
//					Edge checkPointEdge = Graph.U.createEdge(functionNode, checkPoint);
//					checkPointEdge.tag(XCSG.Contains);
//					
//					Edge falseEdge = Graph.U.createEdge(bst.get(bstIndex-1), checkPoint);
//					falseEdge.putAttr(XCSG.conditionValue, false);
//					falseEdge.tag(XCSG.ControlFlow_Edge);
//					falseEdge.tag("bst_edge");
//					falseEdge.tag("switch_edge");
//					
//					bst.add(checkPoint);
//					sizeFlag = false;
//					bstIndex++;
//				}
					bstIndex++;
			}
		}
		
		
		Edge finalDestEdge = Graph.U.createEdge(bst.get(bstIndex-1), finalDest);
		finalDestEdge.putAttr(XCSG.conditionValue, false);
		finalDestEdge.tag("bst_edge");
		finalDestEdge.tag("switch_edge");
		finalDestEdge.tag(XCSG.ControlFlow_Edge);
		finalDest.tag("bst_node");

		return bst;
	}
	
	public static bstNode bstBuilder(ArrayList<caseNode> c, int start, int end) {
		if (start > end) {
			return null;
		}
		
		int mid = (start + end) / 2;
		c.get(mid).getOriginalNode().tag("bst_node");
		bstNode node = new bstNode(c.get(mid).getOriginalNode());
		
		if (node.leftChild == null) {
			Node root = c.get(mid).getOriginalNode();
			Node rootTrueDest = c.get(mid).getToNode();
			Edge tempEdge = Graph.U.createEdge(root, rootTrueDest);
			
			tempEdge.tag(XCSG.ControlFlow_Edge);
			tempEdge.tag("switch_edge");
			
//			node.leftChild = rootTrueDest;
		}
		
			node.leftChild = bstBuilder(c, start, mid-1);
			node.rightChild = bstBuilder(c, mid+1, end);
		
		return node;
	}
	
	
	private static class caseNode{
		private Node originalNode;
		private long lineNumber;
		private int fromAddr; 
		private Node toNode;
		
		public caseNode(Node n, long l, Node t) {
			this.lineNumber = l;
			this.originalNode = n;
			
			this.originalNode.tag(XCSG.ControlFlowCondition);
			this.originalNode.tag("bst_node");
			
//			this.fromAddr = f;
			this.toNode = t;
		}
		
		public Node getToNode() {
			return this.toNode;
		}
		
		public Node getOriginalNode() {
			return this.originalNode;
		}
		
		public void setLineNumber(int l) {
			this.lineNumber = l;
		}
		
		public long getLineNumber() {
			return this.lineNumber;
		}
	
	}
	
	
	private static class bstNode{
		public bstNode leftChild;
		public bstNode rightChild;
		public Node data;
		
		public bstNode(Node current) {
			data = current;
			leftChild = rightChild = null;
		}
	}
	
	private static Long getCSourceLineNumber(Node node) {
		long lineNumber = -1;
		if (node.hasAttr(XCSG.sourceCorrespondence)) {
			SourceCorrespondence sc = (SourceCorrespondence) node.getAttr(XCSG.sourceCorrespondence);
			if (sc != null) {
				lineNumber = sc.startLine;
			}
		}
		return lineNumber;
	}
	
}
