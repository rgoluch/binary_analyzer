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
	
	public static void caseSorter() throws IOException {
		
		String switchPath = "/Users/RyanGoluch/Desktop/Masters_Work/switch_checking/switch_order_checking.csv";
		File switchFile = new File(switchPath);
		BufferedWriter switchWriter = new BufferedWriter(new FileWriter(switchFile));
		switchWriter.write("Function Name, # of Cases, Case Ordering\n");
		
			
		ArrayList<String> functions = switchChecker();		
		for (String s : functions) {
			Q function = my_function(s);
			Q c = my_cfg(function);
			
			ArrayList<Long> nodes = new ArrayList<Long>();
			
			for (Node n : c.eval().nodes()) {
				if (n.taggedWith(XCSG.CaseLabel) || n.taggedWith(XCSG.DefaultCaseLabel)) {
					long l = getCSourceLineNumber(n);
//					caseNode x = new caseNode(n, l);
					nodes.add(l);
				}
			}
			
			for (int i = 0; i < nodes.size(); i++) {
				for (int j = i+1; j < nodes.size(); j++) {
					long temp = nodes.get(i);
					long current = nodes.get(j);
					if (temp > current) {
						nodes.set(i,current);
						nodes.set(j, temp);
					}
				}
			}
			
			switchWriter.write(s + "," + nodes.size() + "," + nodes.toString() + "\n");
			switchWriter.flush();
		}
		
		switchWriter.close();
		
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
		ArrayList<Node> caseNodes = new ArrayList<Node>();
		
		for (Edge e : c.eval().edges().tagged(XCSG.ControlFlow_Edge)) {
			if (e.to().taggedWith(XCSG.ControlFlowSwitchCondition)) {
				continue;
			}
			else if (e.from().taggedWith(XCSG.ControlFlowSwitchCondition)) {
				caseNodes.add(e.to());
				continue;
			}
			else if (e.from().taggedWith(XCSG.DefaultCaseLabel)) {
				Node header = e.to();
				Node tempHeader = Graph.U.createNode();
				
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
			else if (!e.from().taggedWith(XCSG.CaseLabel)) {
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
		
		Q x = my_function(functionNode.getAttr(XCSG.name).toString());
		Q switch_cfg = my_cfg(x);
		return switch_cfg.nodes("switch_graph").induce(Query.universe().edges("switch_edge"));
	}
	
	private static class caseNode{
		private Node originalNode;
		private long lineNumber;
		private int fromAddr; 
		private int toAddr;
		
		public caseNode(Node n, long l, int f, int t) {
			this.lineNumber = l;
			this.originalNode = n;
			this.fromAddr = f;
			this.toAddr = t;
		}
		
		public int getFromAddr() {
			return this.fromAddr;
		}
		
		public int getToAddr() {
			return this.toAddr;
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
