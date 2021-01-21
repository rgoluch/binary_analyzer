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
		ArrayList<caseNode> nodes = new ArrayList<caseNode>();
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
		Map<Node, Node> caseCFGPredecessors = new HashMap<Node, Node>();

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
		ArrayList<caseNode> sortedCases = caseSorter(caseNodes);
		ArrayList<Node> bstNodes = bstCaseNodes(sortedCases, functionNode, defNode, casesAdded);
		ArrayList<Node> falseEdgeAdded = new ArrayList<Node>();

		
		//Handle extra check needed for binary search if more than 3 cases
		if (sortedCases.size() > 3) {
			Node checkPoint = Graph.U.createNode();
			checkPoint.putAttr(XCSG.name, "direction checkpoint");
			checkPoint.tag(XCSG.ControlFlowCondition);
			checkPoint.tag("switch_graph");
			checkPoint.tag("bst_node");
			checkPoint.tag("check");
			
			Edge checkPointEdge = Graph.U.createEdge(functionNode, checkPoint);
			checkPointEdge.tag(XCSG.Contains);
			
			Edge firstFalseEdge = Graph.U.createEdge(bstNodes.get(0), checkPoint);
			firstFalseEdge.tag(XCSG.ControlFlow_Edge);
			firstFalseEdge.tag("switch_edge");
			firstFalseEdge.tag("bst_edge");
			firstFalseEdge.putAttr(XCSG.conditionValue, false);
			falseEdgeAdded.add(bstNodes.get(0));
			
			Edge checkPointTrue = Graph.U.createEdge(checkPoint, bstNodes.get(1));
			checkPointTrue.tag(XCSG.ControlFlow_Edge);
			checkPointTrue.tag("switch_edge");
			checkPointTrue.tag("bst_edge");
			checkPointTrue.putAttr(XCSG.conditionValue, true);
			
			int mid = (bstNodes.size() / 2) + 1;
			
			Edge checkPointFalse = Graph.U.createEdge(checkPoint, bstNodes.get(mid));
			checkPointFalse.tag(XCSG.ControlFlow_Edge);
			checkPointFalse.tag("switch_edge");
			checkPointFalse.tag("bst_edge");
			checkPointFalse.putAttr(XCSG.conditionValue, false);
			
			int i = 1; 
			mid = bstNodes.size() / 2;
			
			while (i < bstNodes.size()) {				
				if (!falseEdgeAdded.contains(bstNodes.get(i))) {
					
					if ((i == mid)) {
						Edge falseEdge = Graph.U.createEdge(bstNodes.get(i), defNode);
						falseEdge.putAttr(XCSG.conditionValue, false);
						falseEdge.tag(XCSG.ControlFlow_Edge);
						falseEdge.tag("bst_edge");
						falseEdge.tag("switch_edge");
						falseEdgeAdded.add(bstNodes.get(i));
					}
					else if (i < bstNodes.size() - 1) {
						Edge falseEdge = Graph.U.createEdge(bstNodes.get(i), bstNodes.get(i+1));
						falseEdge.putAttr(XCSG.conditionValue, false);
						falseEdge.tag(XCSG.ControlFlow_Edge);
						falseEdge.tag("bst_edge");
						falseEdge.tag("switch_edge");
						falseEdgeAdded.add(bstNodes.get(i));
					}
				}
				
				i++;
			}
		}
		else {
			//setting false edges for anything less than 3 cases
			for (int i = 1; i < bstNodes.size(); i++) {
				Edge falseEdge = Graph.U.createEdge(bstNodes.get(i - 1), bstNodes.get(i));
				falseEdge.putAttr(XCSG.conditionValue, false);
				falseEdge.tag(XCSG.ControlFlow_Edge);
				falseEdge.tag("bst_edge");
				falseEdge.tag("switch_edge");
			}
		}
		
		//Have all predecessors point to the first case
		Node firstCase = bstNodes.get(0);
		
		for (Node n : switchPredecessors.values()) {
			Edge predEdge = Graph.U.createEdge(n, firstCase);
			predEdge.tag(XCSG.ControlFlow_Edge);
			predEdge.tag("switch_edge");
		}
		
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
	
	
	
	public static ArrayList<Node> bstCaseNodes(ArrayList<caseNode> nodes, Node functionNode, Node finalDest, Map<Node, Node> casesAdded) {
		ArrayList<Node> bst = new ArrayList<Node>();
		
		int l = 0;
		int r = nodes.size() - 1;
		int mid = (l + r) / 2;
		int bstIndex = 0;		

		
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
				
				//Add to return graph
				Edge containerEdge = Graph.U.createEdge(functionNode, caseCreate);
				containerEdge.tag(XCSG.Contains);
				
				//Set true destination
				Node trueDest = nodes.get(mid).getToNode();
				trueDest.tag("bst_node");
				casesAdded.put(current, trueDest);
				
				Edge trueEdge = Graph.U.createEdge(caseCreate, trueDest);
				trueEdge.tag("bst_edge");
				trueEdge.tag("switch_edge");
				trueEdge.putAttr(XCSG.conditionValue, true);
				trueEdge.tag(XCSG.ControlFlow_Edge);
				
				bstIndex++;
			}
		}
		
		l = 0;
		r = nodes.size() - 1;
		mid = (l + r) / 2;
		
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
				
				//Add to return graph
				Edge containerEdge = Graph.U.createEdge(functionNode, caseCreate);
				containerEdge.tag(XCSG.Contains);
				
				//Set true destination
				Node trueDest = nodes.get(mid).getToNode();
				trueDest.tag("bst_node");
				casesAdded.put(current, trueDest);
				
				Edge trueEdge = Graph.U.createEdge(caseCreate, trueDest);
				trueEdge.tag("bst_edge");
				trueEdge.tag("switch_edge");
				trueEdge.putAttr(XCSG.conditionValue, true);
				trueEdge.tag(XCSG.ControlFlow_Edge);

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
	
	private static class caseNode{
		private Node originalNode;
		private long lineNumber; 
		private Node toNode;
		
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
