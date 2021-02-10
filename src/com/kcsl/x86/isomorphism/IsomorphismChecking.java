package com.kcsl.x86.isomorphism;

import com.ensoftcorp.atlas.core.db.graph.Edge;
import com.ensoftcorp.atlas.core.db.graph.Graph;
import com.ensoftcorp.atlas.core.db.graph.Node;
import com.ensoftcorp.atlas.core.db.set.AtlasSet;
import com.ensoftcorp.atlas.core.query.Q;
import com.ensoftcorp.atlas.core.xcsg.XCSG;

import static com.kcsl.x86.static_function_transform.StaticFunctionChecking.*;
import static com.kcsl.x86.switch_transform.SwitchStatementChecking.*;

import java.util.HashMap;
import java.util.Map;

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
		int label = 1; 
		
		AtlasSet<Node> srcLoopHeaders = srcGraph.eval().nodes().tagged(XCSG.ControlFlowLoopCondition);
		for (Node l : srcLoopHeaders) {
			long children = l.out().tagged("src_induced_edge").size();
			isoNode i = new isoNode(l, children, label);
			label +=1;
			srcIsoNodes.put(l, i);
//			System.out.println("Node: "+ l);
//			System.out.println("Label: "+ label);
			
		}
		
		AtlasSet<Node> srcNodes = srcGraph.eval().nodes();
		for (Node s : srcNodes) {
			if (!srcIsoNodes.containsKey(s)) {
				long children = s.out().tagged("src_induced_edge").size();
				isoNode x = new isoNode(s, children, label);
				label +=1;
				srcIsoNodes.put(s, x);
			}
		}
		
		for(Node k : srcIsoNodes.keySet()) {
			AtlasSet<Edge> outEdges = k.out("src_induced_edge");
			for (Edge e : outEdges) {
				if (e.hasAttr(XCSG.conditionValue)) {
					if (e.getAttr(XCSG.conditionValue).toString().contains("true")) {
						isoNode trueNode = srcIsoNodes.get(e.to());
						isoNode currentNode = srcIsoNodes.get(k);
						currentNode.lChild = trueNode.label;
					}else {
						isoNode falseNode = srcIsoNodes.get(e.to());
						isoNode currentNode = srcIsoNodes.get(k);
						currentNode.rChild = falseNode.label;
					}
				}
			}
		}
		
		for (isoNode z : srcIsoNodes.values()) {
			System.out.println("Src Node: "+z.graphNode.getAttr(XCSG.name));
			System.out.println("Left Child: "+z.lChild);
			System.out.println("Right Child: "+z.rChild);
		}
		
		
	}
	
	private static class isoNode {
		private Node graphNode; 
		private long children; 
		private int lChild;
		private int rChild;
		private int parent;
		private int label;
		private String structure;
		
		public isoNode(Node g, long c, int l) {
			this.graphNode = g;
			this.children = c;
			this.label = l;
//			this.structure = s;
		}
	}
}
