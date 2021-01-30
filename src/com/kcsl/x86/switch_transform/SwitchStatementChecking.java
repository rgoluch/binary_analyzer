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
					switchCount++;
					switchFunctions.add(srcName);
				}
			}
		}
		
		System.out.println("Total number of switch functions: " + switchCount);
		return switchFunctions;
	}
	
	public static ArrayList<caseNode> caseSorter(ArrayList<caseNode> cases) {
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
	}
	
	public static Q switchTransform(String name, Q c) {
		
		//Get the original source CFG
//		Q f = my_function(name);	
//		Q c = my_cfg(f);
		
		AtlasSet<Node> switchNodes = c.eval().nodes().tagged(XCSG.ControlFlowSwitchCondition);
		if (switchNodes.size() == 0) {
			return c;
		}
		
		//Set up for new function node for returned CFG
		Node functionNode = Graph.U.createNode();
		functionNode.putAttr(XCSG.name, "switch_transform_"+name);
		functionNode.tag(XCSG.Function);
		functionNode.tag("switch_graph");
		
		Map<Node,Node> recreatedNodes = new HashMap<Node,Node>();
		ArrayList<caseNode> caseNodes = new ArrayList<caseNode>();
		Map<Integer,Node> switchPredecessors = new HashMap<Integer,Node>();
		Map<Node, Node> caseCFGPredecessors = new HashMap<Node, Node>();
		
		//Key is the predecessor node that is created, value is the address bits of predecessor
		Map<predecessorNode,Integer> switchNodeTracking = new HashMap<predecessorNode,Integer>();
		
		//Used to keep track of the default nodes for each switch block
		Map<Node,Node> defaultNodeTracking = new HashMap<Node,Node>();

//		Node defNode = null;
		
		for (Edge e : c.eval().edges().tagged(XCSG.ControlFlow_Edge)) {
			if (e.to().taggedWith(XCSG.ControlFlowSwitchCondition)) {
				
				Node predecessor = e.from();
				Node recreatedCheck = recreatedNodes.get(predecessor);
				
				if(e.from().taggedWith(XCSG.ControlFlowSwitchCondition)) {
					continue;
				}
				
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
					
					predecessorNode p = new predecessorNode(e.to(), predecessor, tempPred);
					switchNodeTracking.put(p, predecessor.addressBits());
					
				}
				else {
					recreatedCheck.tag("switch_pred");
					switchPredecessors.put(predecessor.addressBits(), recreatedCheck);
					
					predecessorNode p = new predecessorNode(e.to(), predecessor, recreatedCheck);
					switchNodeTracking.put(p, predecessor.addressBits());
				}
				
//				Node switchNode = e.to();
//				
//				for(Edge defEdge : switchNode.out()) {
//					if (defEdge.hasAttr(XCSG.conditionValue)) {
//						if (defEdge.getAttr(XCSG.conditionValue).toString().contains("default")) {
//							Node addedCheck = recreatedNodes.get(defEdge.to());
//							
//							if (addedCheck == null && !defEdge.to().taggedWith(XCSG.ControlFlowSwitchCondition)) {
//								Node tempDef = Graph.U.createNode();
//								tempDef.putAttr(XCSG.name, defEdge.to().getAttr(XCSG.name).toString());
//								tempDef.tag("switch_graph");
//								tempDef.tag("switch_def");
//								tempDef.tag(XCSG.ControlFlow_Node);
//								
//								if (defEdge.to().taggedWith(XCSG.ControlFlowCondition)) {
//									tempDef.tag(XCSG.ControlFlowCondition);
//								}
//								
//								Edge e1 = Graph.U.createEdge(functionNode, tempDef);
//								e1.tag(XCSG.Contains);
//								recreatedNodes.put(defEdge.to(), tempDef);
//								defNode = tempDef;
//							}
//							else if (addedCheck == null && defEdge.to().taggedWith(XCSG.ControlFlowSwitchCondition)) {
//								
//							}
//							else {
//								defNode = addedCheck;
//								defNode.tag("switch_def");
//							}
//						}
//					}
//				}
			}
			else if (e.from().taggedWith(XCSG.CaseLabel) && !e.from().taggedWith(XCSG.DefaultCaseLabel)) {
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
					
					if (trueEval.taggedWith(XCSG.CaseLabel) && !trueEval.taggedWith(XCSG.DefaultCaseLabel)) {
						tempTrue.tag(XCSG.CaseLabel);
					}
					
					Edge e1 = Graph.U.createEdge(functionNode, tempTrue);
					e1.tag(XCSG.Contains);
					recreatedNodes.put(trueEval, tempTrue);
				}
				else {
					tempTrue = recreatedCheck;
				}
				
				AtlasSet<Edge> inEdges = e.from().in(XCSG.ControlFlow_Edge);
				Node switchToCaseNode = null;
				for (Edge i : inEdges) {
					if (i.hasAttr(XCSG.conditionValue)) {
						if (!i.getAttr(XCSG.conditionValue).toString().contains("default")) {
							switchToCaseNode = i.from();
						}
					}
				}
				
				
				long l = getCSourceLineNumber(e.from());
				caseNode x = new caseNode(e.from(), l, tempTrue);
				x.setSwitchNode(switchToCaseNode);
				
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
//					defNode = tempDefault;
					recreatedNodes.put(e.from(), tempDefault);
				}
				else {
					tempDefault = recreatedFromCheck;
//					defNode = tempDefault;
//					defNode.tag("switch_def");
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
					
//					defNode = tempHeader;
					recreatedNodes.put(header, tempHeader);
				}
				else {
					tempHeader = recreatedCheck;
//					defNode = tempHeader;
//					defNode.tag("switch_def");
				}
				
				Edge defaultEdge = Graph.U.createEdge(tempDefault, tempHeader);
				defaultEdge.tag(XCSG.ControlFlow_Edge);
				defaultEdge.tag("switch_edge");
			}
			else if (!e.from().taggedWith(XCSG.CaseLabel) && !e.from().taggedWith(XCSG.ControlFlowSwitchCondition) 
					&& !e.to().taggedWith(XCSG.CaseLabel) && !e.to().taggedWith(XCSG.ControlFlowSwitchCondition)) {
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
				
				if (checkFrom != null && checkTo != null) {
					tempEdge = Graph.U.createEdge(checkFrom, checkTo);
					tempEdge.tag(XCSG.ControlFlow_Edge);
					tempEdge.tag("switch_edge");
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
			
			if (e.to().taggedWith(XCSG.CaseLabel) && !e.to().taggedWith(XCSG.DefaultCaseLabel) && !e.from().taggedWith(XCSG.ControlFlowSwitchCondition)) {
				Node cfgFrom = e.from();
				Node fromCheck = recreatedNodes.get(cfgFrom);
				Node tempCFGFrom = null;
				
				if (fromCheck == null) {
					tempCFGFrom = Graph.U.createNode();
					tempCFGFrom.putAttr(XCSG.name, cfgFrom.getAttr(XCSG.name).toString());
					tempCFGFrom.tag("switch_graph");
					tempCFGFrom.tag(XCSG.ControlFlow_Node);
					
					if (cfgFrom.taggedWith(XCSG.ControlFlowCondition)) {
						tempCFGFrom.tag(XCSG.ControlFlowCondition);
					}
					
					Edge e1 = Graph.U.createEdge(functionNode, tempCFGFrom);
					e1.tag(XCSG.Contains);
					recreatedNodes.put(cfgFrom, tempCFGFrom);
					caseCFGPredecessors.put(e.to(), tempCFGFrom);
				}
				else {
					tempCFGFrom = fromCheck;
					caseCFGPredecessors.put(e.to(), tempCFGFrom);
				}
			}
		}
		
		Map<Node, Node> casesAdded = new HashMap<Node, Node>();
		Map<Node, caseNode> bstToSortedNodes = new HashMap<Node, caseNode>();
		Map<Node, ArrayList<caseNode>> switchCaseRelation = new HashMap<Node, ArrayList<caseNode>>();
		
		for (Node s : switchNodes) {
			ArrayList<caseNode> tempList = new ArrayList<caseNode>();
			
			for (caseNode b : caseNodes) {
				if (b.switchNode.equals(s)) {
					tempList.add(b);
				}
			}
			
			switchCaseRelation.put(s, tempList);
		}
		
		for (Node g : switchCaseRelation.keySet()) {
			ArrayList<caseNode> a = switchCaseRelation.get(g);
			a = caseSorter(a);
			switchCaseRelation.replace(g, a);
		}
		
		ArrayList<Node> bstNodes = bstCaseNodes(switchCaseRelation, functionNode, casesAdded, bstToSortedNodes);
		
		for (Node n : switchNodes) {
			for (Edge e : n.out(XCSG.ControlFlow_Edge)) {
//				if (e.hasAttr(XCSG.conditionValue)) {
				if (e.getAttr(XCSG.conditionValue).toString().contains("default") && !e.to().taggedWith(XCSG.ControlFlowSwitchCondition)) {
					Node toNodeChecking = null;
					
					for (Node r : recreatedNodes.keySet()) {
						if (e.to().equals(r)) {
							toNodeChecking = recreatedNodes.get(r);
							break;
						}
					}
					
					if (toNodeChecking == null) {
						Node tempDefault = Graph.U.createNode();
						tempDefault.putAttr(XCSG.name, e.to().getAttr(XCSG.name).toString());
						tempDefault.tag("switch_graph");
						tempDefault.tag(XCSG.ControlFlow_Node);
						
						if (e.to().taggedWith(XCSG.ControlFlowCondition)) {
							tempDefault.tag(XCSG.ControlFlowCondition);
						}
						if (e.to().taggedWith(XCSG.controlFlowExitPoint)) {
							tempDefault.tag(XCSG.controlFlowExitPoint);
						}
						
						toNodeChecking = tempDefault;
					}
					
					defaultNodeTracking.put(n, toNodeChecking);
				}
				else if (e.getAttr(XCSG.conditionValue).toString().contains("default") && e.to().taggedWith(XCSG.ControlFlowSwitchCondition)) {
					
					ArrayList<caseNode> sortedCases = switchCaseRelation.get(n);
					
					int mid = (int) e.to().out(XCSG.ControlFlow_Edge).size()/2;
					Node toNodeChecking = e.to();
					
					if (toNodeChecking.taggedWith("switch_graph")) {
						toNodeChecking.untag("switch_graph");
					}

					caseNode s = sortedCases.get(mid);
					if(toNodeChecking.equals(s.switchNode)) {
						toNodeChecking = s.createdNode;
					}
					defaultNodeTracking.put(n, toNodeChecking);
				}
//				}
			}
		}
		
		
		ArrayList<Node> falseEdgeAdded = new ArrayList<Node>();

		for (Node s : switchCaseRelation.keySet()) {
			
			ArrayList<caseNode> cases = switchCaseRelation.get(s);
			
			if (cases.size() > 3) {
				Node checkPoint = Graph.U.createNode();
				checkPoint.putAttr(XCSG.name, "direction checkpoint");
				checkPoint.tag(XCSG.ControlFlowCondition);
				checkPoint.tag("switch_graph");
				checkPoint.tag("bst_node");
				checkPoint.tag("check");
				
				Edge checkPointEdge = Graph.U.createEdge(functionNode, checkPoint);
				checkPointEdge.tag(XCSG.Contains);
				
				Edge firstFalseEdge = Graph.U.createEdge(cases.get(0).createdNode, checkPoint);
				firstFalseEdge.tag(XCSG.ControlFlow_Edge);
				firstFalseEdge.tag("switch_edge");
				firstFalseEdge.tag("bst_edge");
				firstFalseEdge.putAttr(XCSG.conditionValue, false);
				falseEdgeAdded.add(bstNodes.get(0));
				
				Edge checkPointTrue = Graph.U.createEdge(checkPoint, cases.get(1).createdNode);
				checkPointTrue.tag(XCSG.ControlFlow_Edge);
				checkPointTrue.tag("switch_edge");
				checkPointTrue.tag("bst_edge");
				checkPointTrue.putAttr(XCSG.conditionValue, true);
				
				int mid = (cases.size() / 2) + 1;
				
				Edge checkPointFalse = Graph.U.createEdge(checkPoint, cases.get(mid).createdNode);
				checkPointFalse.tag(XCSG.ControlFlow_Edge);
				checkPointFalse.tag("switch_edge");
				checkPointFalse.tag("bst_edge");
				checkPointFalse.putAttr(XCSG.conditionValue, false);
				
				int i = 1; 
				mid = cases.size() / 2;
				
				while (i < cases.size()) {	
					if (!falseEdgeAdded.contains(cases.get(i).createdNode) && cases.get(i).createdNode.out(XCSG.ControlFlow_Edge).size() < 2) {
						
						//ADD in default creation
						
						if ((i == mid)) {
							
							Edge falseEdge = Graph.U.createEdge(cases.get(i).createdNode, defaultNodeTracking.get(s));
							falseEdge.putAttr(XCSG.conditionValue, false);
							falseEdge.tag(XCSG.ControlFlow_Edge);
							falseEdge.tag("bst_edge");
							falseEdge.tag("switch_edge");
							falseEdgeAdded.add(cases.get(i).createdNode);
						}
						else if (i < cases.size() - 1) {
							Edge falseEdge = Graph.U.createEdge(cases.get(i).createdNode, cases.get(i+1).createdNode);
							falseEdge.putAttr(XCSG.conditionValue, false);
							falseEdge.tag(XCSG.ControlFlow_Edge);
							falseEdge.tag("bst_edge");
							falseEdge.tag("switch_edge");
							falseEdgeAdded.add(cases.get(i).createdNode);
						}
					}
					i++;
				}
			}
			else {
				for (int i = 1; i < cases.size(); i++) {
					if (cases.get(i-1).createdNode.out(XCSG.ControlFlow_Edge).size() < 2) {
						Edge falseEdge = Graph.U.createEdge(cases.get(i - 1).createdNode, cases.get(i).createdNode);
						falseEdge.putAttr(XCSG.conditionValue, false);
						falseEdge.tag(XCSG.ControlFlow_Edge);
						falseEdge.tag("bst_edge");
						falseEdge.tag("switch_edge");
					}
				}
				
				Node falseEdgeToNode = defaultNodeTracking.get(s);
				
				Edge falseEdge = Graph.U.createEdge(cases.get(cases.size()-1).createdNode, falseEdgeToNode);
				falseEdge.putAttr(XCSG.conditionValue, false);
				falseEdge.tag(XCSG.ControlFlow_Edge);
				falseEdge.tag("bst_edge");
				falseEdge.tag("switch_edge");
			}
		}
		
		
		//ADD in default creation 
		
		//Handle extra check needed for binary search if more than 3 cases
//		if (4 > 3) {
//			Node checkPoint = Graph.U.createNode();
//			checkPoint.putAttr(XCSG.name, "direction checkpoint");
//			checkPoint.tag(XCSG.ControlFlowCondition);
//			checkPoint.tag("switch_graph");
//			checkPoint.tag("bst_node");
//			checkPoint.tag("check");
//			
//			Edge checkPointEdge = Graph.U.createEdge(functionNode, checkPoint);
//			checkPointEdge.tag(XCSG.Contains);
//			
//			Edge firstFalseEdge = Graph.U.createEdge(bstNodes.get(0), checkPoint);
//			firstFalseEdge.tag(XCSG.ControlFlow_Edge);
//			firstFalseEdge.tag("switch_edge");
//			firstFalseEdge.tag("bst_edge");
//			firstFalseEdge.putAttr(XCSG.conditionValue, false);
//			falseEdgeAdded.add(bstNodes.get(0));
//			
//			Edge checkPointTrue = Graph.U.createEdge(checkPoint, bstNodes.get(1));
//			checkPointTrue.tag(XCSG.ControlFlow_Edge);
//			checkPointTrue.tag("switch_edge");
//			checkPointTrue.tag("bst_edge");
//			checkPointTrue.putAttr(XCSG.conditionValue, true);
//			
//			int mid = (bstNodes.size() / 2) + 1;
//			
//			Edge checkPointFalse = Graph.U.createEdge(checkPoint, bstNodes.get(mid));
//			checkPointFalse.tag(XCSG.ControlFlow_Edge);
//			checkPointFalse.tag("switch_edge");
//			checkPointFalse.tag("bst_edge");
//			checkPointFalse.putAttr(XCSG.conditionValue, false);
//			
//			int i = 1; 
//			mid = bstNodes.size() / 2;
//			
//			while (i < bstNodes.size()) {	
//				if (!falseEdgeAdded.contains(bstNodes.get(i))) {
//					
//					caseNode b1 = bstToSortedNodes.get(bstNodes.get(i));
//					caseNode b2 = bstToSortedNodes.get(bstNodes.get(i+1));
//					Node switch1 = b1.switchNode;
//					Node switch2 = b2.switchNode;
//					if (switch1.equals(switch2)) {
//						if (i < bstNodes.size() - 1) {
//							Edge falseEdge = Graph.U.createEdge(bstNodes.get(i), bstNodes.get(i+1));
//							falseEdge.putAttr(XCSG.conditionValue, false);
//							falseEdge.tag(XCSG.ControlFlow_Edge);
//							falseEdge.tag("bst_edge");
//							falseEdge.tag("switch_edge");
//							falseEdgeAdded.add(bstNodes.get(i));
//						}
//					}else {
//						Node defNode = defaultNodeTracking.get(switch2);
//						Edge falseEdge = Graph.U.createEdge(bstNodes.get(i), defNode);
//						
//						falseEdge.putAttr(XCSG.conditionValue, false);
//						falseEdge.tag(XCSG.ControlFlow_Edge);
//						falseEdge.tag("bst_edge");
//						falseEdge.tag("switch_edge");
//						falseEdgeAdded.add(bstNodes.get(i));
//					}
//					
//					
////					if ((i == mid)) {
////						Edge falseEdge = Graph.U.createEdge(bstNodes.get(i), defNode);
////						falseEdge.putAttr(XCSG.conditionValue, false);
////						falseEdge.tag(XCSG.ControlFlow_Edge);
////						falseEdge.tag("bst_edge");
////						falseEdge.tag("switch_edge");
////						falseEdgeAdded.add(bstNodes.get(i));
////					}
////					else 
//				}
//				
//				i++;
//			}
//		}
//		else {
//			//setting false edges for anything less than 3 cases
//			for (int i = 1; i < bstNodes.size(); i++) {
//				Edge falseEdge = Graph.U.createEdge(bstNodes.get(i - 1), bstNodes.get(i));
//				falseEdge.putAttr(XCSG.conditionValue, false);
//				falseEdge.tag(XCSG.ControlFlow_Edge);
//				falseEdge.tag("bst_edge");
//				falseEdge.tag("switch_edge");
//			}
//		}
		
		
		for (Node k : switchNodes) {
			for (predecessorNode p : switchNodeTracking.keySet()) {
				if (p.switchNode.equals(k)) {
					Node first = switchCaseRelation.get(k).get(0).createdNode;
					Edge predEdge = Graph.U.createEdge(p.createdNode, first);
					predEdge.tag(XCSG.ControlFlow_Edge);
					predEdge.tag("switch_edge");
				}
			}
		}
		
		
		//Have all predecessors point to the first case
//		Node firstCase = bstNodes.get(0);
//		
//		for (Node n : switchPredecessors.values()) {
//			Edge predEdge = Graph.U.createEdge(n, firstCase);
//			predEdge.tag(XCSG.ControlFlow_Edge);
//			predEdge.tag("switch_edge");
//		}
		
		//Add fall through edges (i.e. if cases are consecutive with no break or return)
		for (Node n : caseCFGPredecessors.keySet()) {
			Node cfgPred = caseCFGPredecessors.get(n);
			Node caseAdded = casesAdded.get(n);
			
			Edge cfgPredEdge = Graph.U.createEdge(cfgPred, caseAdded);
			cfgPredEdge.tag(XCSG.ControlFlow_Edge);
			cfgPredEdge.tag("switch_edge");
		}
		
		Q x = my_function(functionNode.getAttr(XCSG.name).toString());
		Q switch_cfg = my_cfg(x);
		return switch_cfg.nodes("switch_graph").induce(Query.universe().edges("switch_edge"));
	}
	
	
	
	public static ArrayList<Node> bstCaseNodes(Map<Node, ArrayList<caseNode>> nodesMap, Node functionNode, Map<Node, Node> casesAdded, Map<Node, caseNode> bstSorted) {
		ArrayList<Node> bst = new ArrayList<Node>();
		
		for (Node s : nodesMap.keySet()) {
			
			ArrayList<caseNode> nodes = nodesMap.get(s);
			ArrayList<caseNode> replacementList = new ArrayList<caseNode>();
			
			int l = 0;
			int r = nodes.size() - 1;
			int mid = (l + r) / 2;
			
			
			for (int j = mid; j < nodes.size(); j++) {
				Node current = nodes.get(j).getOriginalNode();
				Node caseCreate = Graph.U.createNode();
				
				//Create the case condition
				caseCreate.putAttr(XCSG.name, current.getAttr(XCSG.name).toString());
				caseCreate.tag(XCSG.ControlFlowCondition);
				caseCreate.tag("switch_graph");
				caseCreate.tag("bst_node");
				
				//Add to array for size check
				if (casesAdded.get(current) == null) {
					bst.add(caseCreate);
					
					nodes.get(j).setCreatedNode(caseCreate);
					bstSorted.put(caseCreate, nodes.get(j));
					replacementList.add(nodes.get(j));
					
					//Add to return graph
					Edge containerEdge = Graph.U.createEdge(functionNode, caseCreate);
					containerEdge.tag(XCSG.Contains);
					
					//Set true destination
					Node trueDest = nodes.get(j).getToNode();
					
					if (trueDest.taggedWith(XCSG.CaseLabel)) {
						for (int z = 0; z < nodes.size(); z++) {
							if (nodes.get(z).originalNode.getAttr(XCSG.name).toString().contains(trueDest.getAttr(XCSG.name).toString())) {
								trueDest = nodes.get(z).toNode;
								
								Edge trueEdge = Graph.U.createEdge(caseCreate, trueDest);
								trueEdge.tag("bst_edge");
								trueEdge.tag("switch_edge");
								trueEdge.putAttr(XCSG.conditionValue, false);
								trueEdge.tag(XCSG.ControlFlow_Edge);
							}
						}
					}
					
					trueDest.tag("bst_node");
					casesAdded.put(current, trueDest);
					
					Edge trueEdge = Graph.U.createEdge(caseCreate, trueDest);
					trueEdge.tag("bst_edge");
					trueEdge.tag("switch_edge");
					trueEdge.putAttr(XCSG.conditionValue, true);
					trueEdge.tag(XCSG.ControlFlow_Edge);
				}
			}
			for (int i = mid-1; i >= 0; i--) {
				Node currentI = nodes.get(i).getOriginalNode();
				Node caseCreateI = Graph.U.createNode();
				
				//Create the case condition
				caseCreateI.putAttr(XCSG.name, currentI.getAttr(XCSG.name).toString());
				caseCreateI.tag(XCSG.ControlFlowCondition);
				caseCreateI.tag("switch_graph");
				caseCreateI.tag("bst_node");
				
				//Add to array for size check
				if (casesAdded.get(currentI) == null) {
					bst.add(caseCreateI);
					
					nodes.get(i).setCreatedNode(caseCreateI);
					bstSorted.put(caseCreateI, nodes.get(i));
					replacementList.add(nodes.get(i));
					
					//Add to return graph
					Edge containerEdge = Graph.U.createEdge(functionNode, caseCreateI);
					containerEdge.tag(XCSG.Contains);
					
					//Set true destination
					Node trueDest = nodes.get(i).getToNode();
					
					if (trueDest.taggedWith(XCSG.CaseLabel)) {
						for (int z = 0; z < nodes.size(); z++) {
							if (nodes.get(z).originalNode.getAttr(XCSG.name).toString().contains(trueDest.getAttr(XCSG.name).toString())) {
								trueDest = nodes.get(z).getToNode();
								
								Edge trueEdge = Graph.U.createEdge(caseCreateI, trueDest);
								trueEdge.tag("bst_edge");
								trueEdge.tag("switch_edge");
								trueEdge.putAttr(XCSG.conditionValue, false);
								trueEdge.tag(XCSG.ControlFlow_Edge);
							}
						}
					}
					
					trueDest.tag("bst_node");
					casesAdded.put(currentI, trueDest);
					
					Edge trueEdge = Graph.U.createEdge(caseCreateI, trueDest);
					trueEdge.tag("bst_edge");
					trueEdge.tag("switch_edge");
					trueEdge.putAttr(XCSG.conditionValue, true);
					trueEdge.tag(XCSG.ControlFlow_Edge);
				}
			}
			
			nodesMap.replace(s, replacementList);
		}
		
		
		
//		while(bstIndex < nodes.size()) {
//			
//			if (toggle) {
//				
//				if (upperL > upperR) {
//					toggle = false;
//					continue;
//				}
//				
//				
//				Node current = nodes.get(upperMid).getOriginalNode();
//				Node caseCreate = Graph.U.createNode();
//				
//				//Create the case condition
//				caseCreate.putAttr(XCSG.name, current.getAttr(XCSG.name).toString());
//				caseCreate.tag(XCSG.ControlFlowCondition);
//				caseCreate.tag("switch_graph");
//				caseCreate.tag("bst_node");
//				upperMid = (upperL + upperR)/2;
//				upperL = upperMid+1; 
//				
//				//Add to array for size check
//				if (casesAdded.get(current) == null) {
//					bst.add(caseCreate);
//					
//					nodes.get(mid).setCreatedNode(caseCreate);
//					bstSorted.put(caseCreate, nodes.get(mid));
//					
//					//Add to return graph
//					Edge containerEdge = Graph.U.createEdge(functionNode, caseCreate);
//					containerEdge.tag(XCSG.Contains);
//					
//					//Set true destination
//					Node trueDest = nodes.get(mid).getToNode();
//					trueDest.tag("bst_node");
//					casesAdded.put(current, trueDest);
//					
//					Edge trueEdge = Graph.U.createEdge(caseCreate, trueDest);
//					trueEdge.tag("bst_edge");
//					trueEdge.tag("switch_edge");
//					trueEdge.putAttr(XCSG.conditionValue, true);
//					trueEdge.tag(XCSG.ControlFlow_Edge);
//					
//					bstIndex++;
//				}
//				toggle = false;
//			}else if (!toggle && lowerL <= lowerR){
//				
//				Node current = nodes.get(lowerMid).getOriginalNode();
//				Node caseCreate = Graph.U.createNode();
//				
//				//Create the case condition
//				caseCreate.putAttr(XCSG.name, current.getAttr(XCSG.name).toString());
//				caseCreate.tag(XCSG.ControlFlowCondition);
//				caseCreate.tag("switch_graph");
//				caseCreate.tag("bst_node");
//				
//				lowerMid = (lowerL + lowerR)/2;
//				lowerR = lowerMid-1; 
//				
//				//Add to array for size check
//				if (casesAdded.get(current) == null) {
//					bst.add(caseCreate);
//					
//					nodes.get(lowerMid).setCreatedNode(caseCreate);
//					bstSorted.put(caseCreate, nodes.get(lowerMid));
//					
//					//Add to return graph
//					Edge containerEdge = Graph.U.createEdge(functionNode, caseCreate);
//					containerEdge.tag(XCSG.Contains);
//					
//					//Set true destination
//					Node trueDest = nodes.get(lowerMid).getToNode();
//					trueDest.tag("bst_node");
//					casesAdded.put(current, trueDest);
//					
//					Edge trueEdge = Graph.U.createEdge(caseCreate, trueDest);
//					trueEdge.tag("bst_edge");
//					trueEdge.tag("switch_edge");
//					trueEdge.putAttr(XCSG.conditionValue, true);
//					trueEdge.tag(XCSG.ControlFlow_Edge);
//					
//					bstIndex++;
//				}
//				toggle = true;
//			}
//			
//		}
		
		
//		while(l <= r) {
//			mid = (l + r)/2;
//			Node current = nodes.get(mid).getOriginalNode();
//			Node caseCreate = Graph.U.createNode();
//			
//			//Create the case condition
//			caseCreate.putAttr(XCSG.name, current.getAttr(XCSG.name).toString());
//			caseCreate.tag(XCSG.ControlFlowCondition);
//			caseCreate.tag("switch_graph");
//			caseCreate.tag("bst_node");
//			
//			l = mid+1; 
//			
//			//Add to array for size check
//			if (casesAdded.get(current) == null) {
//				bst.add(caseCreate);
//				
//				nodes.get(mid).setCreatedNode(caseCreate);
//				bstSorted.put(caseCreate, nodes.get(mid));
//				
//				//Add to return graph
//				Edge containerEdge = Graph.U.createEdge(functionNode, caseCreate);
//				containerEdge.tag(XCSG.Contains);
//				
//				//Set true destination
//				Node trueDest = nodes.get(mid).getToNode();
//				trueDest.tag("bst_node");
//				casesAdded.put(current, trueDest);
//				
//				Edge trueEdge = Graph.U.createEdge(caseCreate, trueDest);
//				trueEdge.tag("bst_edge");
//				trueEdge.tag("switch_edge");
//				trueEdge.putAttr(XCSG.conditionValue, true);
//				trueEdge.tag(XCSG.ControlFlow_Edge);
//				
//				bstIndex++;
//			}
//		}
//		
//		l = 0;
//		r = nodes.size() - 1;
//		mid = (l + r) / 2;
//		
//		while(l <= r) {
//			mid = (l + r)/2;
//			Node current = nodes.get(mid).getOriginalNode();
//			Node caseCreate = Graph.U.createNode();
//			
//			//Create the case condition
//			caseCreate.putAttr(XCSG.name, current.getAttr(XCSG.name).toString());
//			caseCreate.tag(XCSG.ControlFlowCondition);
//			caseCreate.tag("switch_graph");
//			caseCreate.tag("bst_node");
//			
//			r = mid-1; 
//			
//			//Add to array for size check
//			if (casesAdded.get(current) == null) {
//				bst.add(caseCreate);
//				
//				nodes.get(mid).setCreatedNode(caseCreate);
//				bstSorted.put(caseCreate, nodes.get(mid));
//				
//				//Add to return graph
//				Edge containerEdge = Graph.U.createEdge(functionNode, caseCreate);
//				containerEdge.tag(XCSG.Contains);
//				
//				//Set true destination
//				Node trueDest = nodes.get(mid).getToNode();
//				trueDest.tag("bst_node");
//				casesAdded.put(current, trueDest);
//				
//				Edge trueEdge = Graph.U.createEdge(caseCreate, trueDest);
//				trueEdge.tag("bst_edge");
//				trueEdge.tag("switch_edge");
//				trueEdge.putAttr(XCSG.conditionValue, true);
//				trueEdge.tag(XCSG.ControlFlow_Edge);
//
//				bstIndex++;
//			}
//		}
		
		
//		Edge finalDestEdge = Graph.U.createEdge(bst.get(bstIndex-1), finalDest);
//		finalDestEdge.putAttr(XCSG.conditionValue, false);
//		finalDestEdge.tag("bst_edge");
//		finalDestEdge.tag("switch_edge");
//		finalDestEdge.tag(XCSG.ControlFlow_Edge);
//		finalDest.tag("bst_node");

		return bst;
	}
	
	private static class caseNode{
		private Node originalNode;
		private long lineNumber; 
		private Node toNode;
		private Node createdNode;
		private Node switchNode;
		
		public caseNode(Node n, long l, Node t) {
			this.lineNumber = l;
			this.originalNode = n;
			this.originalNode.tag(XCSG.ControlFlowCondition);
			this.originalNode.tag("bst_node");
			this.toNode = t;
		}
		
		public Node getToNode() {
			return this.toNode;
		}
		
		public Node getOriginalNode() {
			return this.originalNode;
		}
		
		public long getLineNumber() {
			return this.lineNumber;
		}
		
		public void setCreatedNode(Node n) {
			this.createdNode = n;
		}
		
		public void setSwitchNode(Node n) {
			this.switchNode = n;
		}
	
	}
	
	private static class predecessorNode{
		private Node switchNode;
		private Node predNode; 
		private Node createdNode;
		
		public predecessorNode(Node s, Node p, Node c) {
			this.switchNode = s;
			this.createdNode = c;
			this.predNode = p;
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
