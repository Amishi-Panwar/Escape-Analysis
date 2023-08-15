package submit_a2;

import java.util.ArrayList;
import java.util.HashMap;
import java.util.HashSet;
import java.util.Iterator;
import java.util.LinkedList;
import java.util.List;
import java.util.Map;
import java.util.Map.Entry;

import dont_submit.EscapeQuery;

import java.util.Queue;
import java.util.Set;

import soot.ArrayType;
import soot.Body;
import soot.BodyTransformer;
import soot.Local;
import soot.MethodOrMethodContext;
import soot.RefLikeType;
import soot.Scene;
import soot.SceneTransformer;
import soot.SootClass;
import soot.SootField;
import soot.SootMethod;
import soot.Unit;
import soot.Value;
import soot.ValueBox;
import soot.VoidType;
import soot.jimple.DefinitionStmt;
import soot.jimple.InstanceFieldRef;
import soot.jimple.InstanceInvokeExpr;
import soot.jimple.InvokeExpr;
import soot.jimple.InvokeStmt;
import soot.jimple.NewExpr;
import soot.jimple.SpecialInvokeExpr;
import soot.jimple.Stmt;
import soot.jimple.VirtualInvokeExpr;
import soot.jimple.internal.JEnterMonitorStmt;
import soot.jimple.internal.JInvokeStmt;
import soot.jimple.internal.JSpecialInvokeExpr;
import soot.jimple.internal.JVirtualInvokeExpr;
import soot.jimple.toolkits.callgraph.CallGraph;
import soot.jimple.toolkits.callgraph.Edge;
import soot.toolkits.graph.BriefUnitGraph;
import soot.toolkits.graph.UnitGraph;
import soot.util.Chain;


class RhoSigmaEscapeMap{
	//rho(x)->Set<Ref> == Map<x,Set<Ref>>
	Map<String,Set<String>>stack;
		
	//sigma(o1,f)->Set<Ref> == Map<o1,Map<field,Set<Ref>>>
	Map<String,Map<String ,Set<String> >> heap;
	
	//Set containing escaped objects
	Set<String> escapeMap;
	
	public RhoSigmaEscapeMap(){
		this.stack = new HashMap<>();
		this.heap = new HashMap<>();
		this.escapeMap = new HashSet<>();
	}
	
	//return set of ref pointed by var
	public Set<String> rho(String var){
		return stack.get(var);
	}
		
	//return set of ref pointed by field
	public Set<String> sigma(String var, String field){
		Set<String> set = new HashSet<>();
		for(String ref: this.stack.get(var)){
			set.addAll(heap.get(ref).get(field));
		}
		return set;
	}
	
}

class InSummary{
	
	//rho(x)->Set<Ref> == Map<x,Set<Ref>>
	Map<String,Set<String>>stack;
	
	//sigma(o1,f)->Set<Ref> == Map<o1,Map<field,Set<Ref>>>
	Map<String,Map<String ,Set<String> >> heap;
	
	//Set containing escaped objects
	Set<String> escapeMap;

	public InSummary(){
		this.stack = new HashMap<>();
		this.heap = new HashMap<>();
		this.escapeMap = new HashSet<>();
		
	}
}

class OutSummary{
	
		//sigma(o1,f)->Set<Ref> == Map<o1,Map<field,Set<Ref>>>
		Map<String,Map<String ,Set<String> >> heap;
		
		//Set containing escaped objects
		Set<String> escapeMap;
		
		//Set containing objects pointed by return value variable
		Set<String> returnValues;
		
		public OutSummary(){
			this.heap = new HashMap<>();
			this.escapeMap = new HashSet<>();
			this.returnValues = new HashSet<>();
		}
}


public class EscapeAnalysis extends SceneTransformer{

	
    //-----------------------------------------------------------------------------------
	//  og-> global set 
		Set<String> ogSet;
    //------------------------------------------------------------------------------------
	
	
	String className;
	String methodName;
	SootMethod sootMethod;
	
	//list of user classes that extend thread
	List<String> threadExtendClasses;
	
	//to store count for creating new object 
	int objinit=1;
	
	//to mark new stmts visited and store its ref variable
	Map<String,RhoSigmaEscapeMap> visited = new HashMap<>();
	
	//call graph 
	CallGraph cg;
	
	//worklist of methods
	Set<SootMethod>methodWorklist;
//	List<SootMethod> methodWorklist;
	
	Chain<SootClass> allClassesInProgram;
	//map that contains outSummary of methods
	Map<SootMethod, OutSummary> mapOfOutSummary = new HashMap<>();
	
	//map that contains inSummary of methods
	Map<SootMethod, InSummary> mapOfInSummary = new HashMap<>();
	
	//store answers
	Map<String , String> finalAnswers = new HashMap<>();
	
	@Override
	protected synchronized void internalTransform(String phaseName, Map<String, String> options) {
		/*
		 * Implement your escape analysis here
		 */
	
		//call graph from CHA obtained from soot
		cg = Scene.v().getCallGraph();
		
		//Get all classes in program
		allClassesInProgram = Scene.v().getApplicationClasses();
		
//		List<SootClass> filter = new LinkedList(allClassesInProgram);
//		filter.removeIf(c -> c.isLibraryClass());
		
		
		
		List<SootMethod> allMethodsInProgram = new ArrayList<SootMethod>();
		
		//get all user methods of program 
		for(SootClass c: allClassesInProgram) {
			if(!c.isLibraryClass()) {
				for(SootMethod method: c.getMethods()) {
//					if(!method.isConstructor())
						allMethodsInProgram.add(method);
				}
			}
		}
		
		
		
		//say we want to obtain all classes in the scene that extend Thread
		SootClass threadClass = Scene.v().getSootClass("java.lang.Thread");
		List<SootClass> classes = Scene.v().getActiveHierarchy().getSubclassesOf(threadClass);
		
		 List<SootClass> filteredClass = new LinkedList<SootClass>(classes);
		 filteredClass.removeIf(c -> c.isLibraryClass());
		 threadExtendClasses = new ArrayList<>();
		for(int i=0; i<filteredClass.size();i++) {
			
			threadExtendClasses.add(filteredClass.get(i).toString());
		}

		
		ogSet = new HashSet<>();;
		ogSet.add("og");
		
		//entry point- main method
		SootMethod mainMethod = Scene.v().getMainMethod();
		
		for(SootMethod method : allMethodsInProgram){
			mapOfInSummary.put(method, new InSummary());
			mapOfOutSummary.put(method, new OutSummary());
			
		}
		
		//worklist of methods
		
		methodWorklist = new HashSet<>();
//		methodWorklist = new ArrayList<>();
		
		//first add main method
		methodWorklist.add(mainMethod);
		
		
		//iterate method of worklist till it gets empty
		while(!methodWorklist.isEmpty()) {
			
			//pop one method out of worklist
			SootMethod currMethod = methodWorklist.iterator().next();
			methodWorklist.remove(currMethod);
//			System.out.println("____________________________________Method starts_____________________________");
			
			//get body of popped method
			Body b = currMethod.getActiveBody();
			//cfg
			UnitGraph g = new BriefUnitGraph(b);
			className = b.getMethod().getDeclaringClass().toString();
			methodName = b.getMethod().getName();
			
			sootMethod = b.getMethod();
			
			
			
			//map that contains DS for each unit of popped method
			Map<String, RhoSigmaEscapeMap> inUnitDS = new HashMap<>();  //inDS->dfin
			
//			Queue<Unit> unitWorklist = new LinkedList<>();
//			Set<Unit> unitWorklist = new HashSet<>();
			List<Unit> unitWorklist = new ArrayList<>();
			//add head of cfg in workList
//			unitWorklisst.addAll(g.getSuccsOf(g.getHeads().get(0)));
			
//			System.out.println("Method body");
			for(Unit u : g) {
				unitWorklist.add(u);
				String unitName = new String(Integer.toString(u.hashCode()));
				inUnitDS.put(unitName,new RhoSigmaEscapeMap());
				
				if(g.getPredsOf(u).isEmpty()) {
					RhoSigmaEscapeMap updatedInSummary = new RhoSigmaEscapeMap();

					updatedInSummary.stack = new HashMap<>(mapOfInSummary.get(currMethod).stack);
					updatedInSummary.heap = new HashMap<>(mapOfInSummary.get(currMethod).heap);
					updatedInSummary.escapeMap = new HashSet<>(mapOfInSummary.get(currMethod).escapeMap);
					inUnitDS.put(unitName, updatedInSummary);

				}
				
			}
//			System.out.println("___________________________________________");
			
			
			
			//iterate set of units till it gets empty
			while(!unitWorklist.isEmpty()) {
				Unit u = unitWorklist.iterator().next();
	            unitWorklist.remove(u);
//				System.out.println("__________________________________UNIT START______________________________");
			
	            RhoSigmaEscapeMap union = new RhoSigmaEscapeMap();
	            for(Unit pred: g.getPredsOf(u)){
	            	RhoSigmaEscapeMap outPred = findOut(pred, inUnitDS.get(Integer.toString(pred.hashCode())));
	            	unionOfPred(union,copyObject(outPred));
	            	
	            }
	            
	            
	            if(!isSame(inUnitDS.get(Integer.toString(u.hashCode())),union)){
	            	//update inUnitDS for u
	            	unionOfPred(union,inUnitDS.get(Integer.toString(u.hashCode())));
	            	inUnitDS.put(Integer.toString(u.hashCode()), union);
	            	//addSuccessors
	            	for(Unit succ : g.getSuccsOf(u))
	            		unitWorklist.add(succ);
	            }
	            
//	            System.out.println(" ______after union_____");
	            
//	            System.out.println(" ______after union end"+ "_____");
	            
//				System.out.println("__________________________________UNIT ENDS______________________________");
				
			}
			
			RhoSigmaEscapeMap finalRhoSigmaEscapeMap= new RhoSigmaEscapeMap();
			for(Unit u : g) {
				
				if(g.getSuccsOf(u).isEmpty()) {
					
					finalRhoSigmaEscapeMap = copyObject(inUnitDS.get(Integer.toString(u.hashCode())));
					
				}
			}
//			System.out.println("FiNAL");
			OutSummary prevOutSummary = mapOfOutSummary.get(currMethod);
			
			
			if(!isSameOutSummary(prevOutSummary, finalRhoSigmaEscapeMap)) {
//				System.out.println("OUT SUMMARY CHANGED");
				Iterator<Edge> inEdges = cg.edgesInto(currMethod);
				
				//Iterate over all caller methods
				while(inEdges.hasNext()) {
					SootMethod callerMethod = inEdges.next().getSrc().method();
					methodWorklist.add(callerMethod);
					
					OutSummary newOutSummary = new OutSummary();
					newOutSummary.heap = new HashMap<>(finalRhoSigmaEscapeMap.heap);
					newOutSummary.escapeMap = new HashSet<>(finalRhoSigmaEscapeMap.escapeMap);
					mapOfOutSummary.put(callerMethod, newOutSummary);
					
				}
				OutSummary newOutSummary = new OutSummary();
				newOutSummary.heap = new HashMap<>(finalRhoSigmaEscapeMap.heap);
				newOutSummary.escapeMap = new HashSet<>(finalRhoSigmaEscapeMap.escapeMap);
				mapOfOutSummary.put(currMethod, newOutSummary);
				
			}
			
//			System.out.println("____________________________________Method ENDS_____________________________");
						
		}
		for(int i=0;i<A2.queryList.size();i++){
			EscapeQuery q = A2.queryList.get(i);
				String key = q.getClassName()+"_"+q.getMethodName();
				
				for(Entry<String, String> entry: finalAnswers.entrySet()) {
					if(entry.getKey().equals(key)) {
						A2.answers[i] = finalAnswers.get(key);
					}
				}

		}

	}
	
	public synchronized RhoSigmaEscapeMap findOut(Unit u, RhoSigmaEscapeMap in){
		
		RhoSigmaEscapeMap out = copyObject(in);
		
		Stmt s = (Stmt)u;

		if(methodName.equals("<init>")) {
			return out;
		}
		
		//if its a type of definition statement than only do the changes
		if(s instanceof DefinitionStmt){
			
			DefinitionStmt ds = (DefinitionStmt)s;
			
			Value lhs = ds.getLeftOp();
			Value rhs = ds.getRightOp();
			
			if(lhs.getType() instanceof RefLikeType ){
			
				if(rhs.getType() instanceof RefLikeType) {
				
//					if(lhs instanceof Local && (rhs.toString().contains("@parameter") || rhs.toString().contains("@this"))){
//						String lhsVarName = className+"_"+methodName+"_"+lhs.toString(); 
//						out.stack.put(lhsVarName,new HashSet<>(ogSet));
//						return out;
//					}
					
					if(rhs instanceof NewExpr){

						
						String lhsVarName = className+"_"+methodName+"_"+lhs.toString(); 
						
						if(visited.containsKey(Integer.toString(u.hashCode()))) {
//							out.stack.put(lhsVarName, );
							out.stack.put(lhsVarName, new HashSet<>(visited.get(Integer.toString(u.hashCode())).stack.get(lhsVarName)));
							
							//add all fields
							for(String ref: visited.get(Integer.toString(u.hashCode())).stack.get(lhsVarName)){
								out.heap.put(ref, getSuperClassFields(rhs));
							}
							//add escaped obj
							out.escapeMap.addAll(visited.get(Integer.toString(u.hashCode())).escapeMap);
							
						}else {

							String newRef = "o"+objinit;
							objinit++;
							Set<String> newObjSet = new HashSet<>();
							newObjSet.add(newRef);
							
							out.stack.put(lhsVarName, newObjSet);
							visited.put(Integer.toString(u.hashCode()), out);
							
							//add all fields
							for(String ref: visited.get(Integer.toString(u.hashCode())).stack.get(lhsVarName)){
								out.heap.put(ref, getSuperClassFields(rhs));
							}
							
							String objCreated = rhs.getType().toString();
							if(threadExtendClasses.contains(objCreated)) {
								
								out.escapeMap.add(newRef);
								
							}
							
						}
						
						return out;
						
					}else if(rhs instanceof InstanceFieldRef){
//						x = y.f;
						//!done
//						System.out.println("Inside load statement");
						String lhsVarName = className+"_"+methodName+"_"+lhs.toString(); 
						
						Value var = ((InstanceFieldRef) rhs).getBase();
						String field = ((InstanceFieldRef) rhs).getField().getName(); 
						String rhsVarName = className+"_"+methodName+"_"+var;
						if(!in.stack.containsKey(rhsVarName))
							return out;
						
						//if rho of y contains og then fields of og will also be og
						if(in.stack.get(rhsVarName).contains("og")) {
							out.stack.put(rhsVarName, new HashSet<>(ogSet));
							out.stack.put(lhsVarName, new HashSet<>(ogSet));
							
							return out;
						}
						
						//if rho of y contains any escaped obj then x will be og
						for(String obj: in.stack.get(rhsVarName)) {
							if(in.escapeMap.contains(obj)) {
								out.stack.put(lhsVarName, new HashSet<>(ogSet));
								return out;
							}
						}
						
						Set<String> allFieldsOfYdotF = new HashSet<>();
						for(String obj: in.stack.get(rhsVarName)) {
							if(in.heap.containsKey(obj)) {
								if(in.heap.get(obj).containsKey(field)){
									allFieldsOfYdotF.addAll(in.heap.get(obj).get(field));
								}
							}
						}
						
						out.stack.put(lhsVarName, allFieldsOfYdotF);
						
						return out;
						
					}else if(lhs instanceof InstanceFieldRef){
						//STORE
						//x.f = y;
//						System.out.println("inside x.f= y");
						Value var = ((InstanceFieldRef) lhs).getBase();
						String field = ((InstanceFieldRef) lhs).getField().getName();
						String lhsVarName = className+"_"+methodName+"_"+var;
						String rhsVarName = className+"_"+methodName+"_"+rhs.toString(); 
						
						
						if(!in.stack.containsKey(lhsVarName)) {
							return out;
						}
						
						
						//if f is static field-- set y and all reachable obj from y to escaped
						if(((InstanceFieldRef) lhs).getField().isStatic()) {
							
							Set<String> reachableObjFromRhs = reachable(rhsVarName, in);
							out.escapeMap.addAll(in.rho(rhsVarName));
							out.escapeMap.addAll(reachableObjFromRhs);
							
							return out;
						}
						
						//if x is escaped-- y and reachable objs from y will get escaped
						for(String obj: in.stack.get(lhsVarName)) {
							if(in.escapeMap.contains(obj)) {
								Set<String> reachableObjFromRhs = reachable(rhsVarName, in);
								out.escapeMap.addAll(reachableObjFromRhs);
								out.escapeMap.addAll(in.rho(rhsVarName));
								
								return out;
							}
						}
						
						if(in.stack.containsKey(rhsVarName)) {
							//if x is og we cant access fields og
							if(in.stack.get(lhsVarName).contains("og")) {
								
								return out;
							}
						}
						
						if(in.stack.containsKey(rhsVarName)) {
							//if y is og directly set fields of x to og
							if(in.stack.get(rhsVarName).contains("og")) {
								out.stack.put(rhsVarName, new HashSet<>(ogSet));
								for(String obj: in.stack.get(lhsVarName)) {
									out.heap.get(obj).put(field, new HashSet<>(ogSet));
								}
								
								return out;
							}
						}
			
							//weak update only
							for(String obj: in.stack.get(lhsVarName)){
								if(in.heap.containsKey(obj)) {
									if(in.heap.get(obj).containsKey(field)){
										if(in.stack.containsKey(rhsVarName))
											out.heap.get(obj).get(field).addAll(in.stack.get(rhsVarName));
									}else {
										if(in.stack.containsKey(rhsVarName))
											out.heap.get(obj).put(field, new HashSet<>(in.stack.get(rhsVarName)));
									}
								}else {
									Map<String, Set<String>> newMap = new HashMap<>();
									if(in.stack.containsKey(rhsVarName))
										newMap.put(field, new HashSet<>(in.stack.get(rhsVarName)));
									out.heap.put(obj, newMap);
								}
							}
							
						
						return out;						
						
						
					}else if(lhs instanceof Local && rhs instanceof Local){
						//x =y
//						System.out.println("copy state"+ u);
						String lhsVarName = className+"_"+methodName+"_"+lhs.toString(); 
						String rhsVarName = className+"_"+methodName+"_"+rhs.toString(); 
						
						if(in.stack.isEmpty())
							return out;
						//if y contains og directly set x to og
						if(in.stack.containsKey(rhsVarName) && in.stack.get(rhsVarName).contains("og")) {
							out.stack.put(lhsVarName,new HashSet<>(ogSet));
							return out;
						}
						
						//if it containsKey or not, no matter what we have to put key
						if(out.stack.containsKey(rhsVarName)) {
							out.stack.put(lhsVarName,new HashSet<>(out.stack.get(rhsVarName)));
						}
						
						return out;
						
						
					}else if(rhs.getType() instanceof ArrayType){
						
					}else if(ds.containsFieldRef()){
//						System.out.println( " static field");
						String rhsVarName = className+"_"+methodName+"_"+rhs.toString(); 
						
						Set<String> reachableObjFromRhs = reachable(rhsVarName, in);
						if(in.stack.containsKey(rhsVarName))
							out.escapeMap.addAll(in.stack.get(rhsVarName));
						out.escapeMap.addAll(reachableObjFromRhs);
						
						return out;
					}else if(ds.containsInvokeExpr()){
//						x=y.foo()
//						System.out.println("Inside x=y.foo()");				
						
					
						return out;
					}
					
					return out;
				}
			}else {
			
				return out;
			}

		}else if (s.containsInvokeExpr() && s.getInvokeExpr().getMethod().getReturnType().equals(VoidType.v())) {
		    //This is a void function call
			
//			//x.foo(); void return type
//			System.out.println("x.foo void type");
			InstanceInvokeExpr iInvokeExpr= (InstanceInvokeExpr)s.getInvokeExpr();
			Value baseVar = iInvokeExpr.getBase();
			
			// get all outgoing edges from the method
			Iterator<Edge> outGoingEdges = cg.edgesOutOf(u);
			
			while(outGoingEdges.hasNext()) {
				
				SootMethod targetMethod = outGoingEdges.next().getTgt().method();
				if(!targetMethod.toString().contains("java.") && !targetMethod.toString().contains("jdk.") && !targetMethod.getName().equals("start") &&!targetMethod.getName().equals("join") && !targetMethod.getName().equals("notify") && !targetMethod.getName().equals("notifyAll") && !targetMethod.getName().equals("wait") ){
					if(!targetMethod.isConstructor()) {
						unionOfOutSummary(out,mapOfOutSummary.get(targetMethod), baseVar);
					}
				}
			}
			
			outGoingEdges = cg.edgesOutOf(u);
			//iterate over all the possible functions can be called as per CHA
			while(outGoingEdges.hasNext()){

				SootMethod targetMethod = outGoingEdges.next().getTgt().method();
			
				if(!targetMethod.toString().contains("java.") && !targetMethod.toString().contains("jdk.") && !targetMethod.getName().equals("start") &&!targetMethod.getName().equals("join") && !targetMethod.getName().equals("notify") && !targetMethod.getName().equals("notifyAll") && !targetMethod.getName().equals("wait") ){
						
					if(!targetMethod.isConstructor()) {
						
						Local thisOfTarget = targetMethod.getActiveBody().getThisLocal();
					
						InSummary prevInSummary = mapOfInSummary.get(targetMethod);
						
						if(!isInSummarySame(out, targetMethod, prevInSummary, baseVar, (Value)thisOfTarget)) {
							//add target function to methodWorklist
		//					System.out.println("In summary different");
							methodWorklist.add(targetMethod);
							
							unionOfInSummary(prevInSummary, out, targetMethod, baseVar, (Value)thisOfTarget);
							
							mapOfInSummary.put(targetMethod, prevInSummary);
						}
						
						return out;
					}
				}
			
			}
		}else if(s instanceof JEnterMonitorStmt){
			JEnterMonitorStmt jstmt = (JEnterMonitorStmt)s;
			
			Value syncVar = jstmt.getOp();
			String syncVarName = className +"_"+ methodName + "_" + syncVar.toString();
			String ansKeyName = className +"_"+ methodName;
			
			if(out.stack.containsKey(syncVarName)){
			if(out.stack.get(syncVarName).contains("og"))
				finalAnswers.put(ansKeyName, "No");
			else {
				for(String obj: out.stack.get(syncVarName)) {
					
					if(out.escapeMap.contains(obj)) {
						finalAnswers.put(ansKeyName, "No");
						break;
					}else {
						finalAnswers.put(ansKeyName, "Yes");
					}
				}
			}
			}
			return out;
		}else {
			
			return out;
		}
		
		return out;
	}
	
//	public synchronized void printInSummary(InSummary prevInSummary) {
//		System.out.println("RHO InSummary");
//		prevInSummary.stack.entrySet().forEach(entry -> {
//		    System.out.println(entry.getKey() + " " + entry.getValue());
//		});
//		
//		System.out.println("SIGMAA InSummary");
//		prevInSummary.heap.entrySet().forEach(entry -> {
//		    System.out.println(entry.getKey() + " " + entry.getValue());
//		});
//		System.out.println("ESCAPE MAP InSummary");
//		System.out.println(prevInSummary.escapeMap); 
//		
//	}
//	
	void unionOfInSummary(InSummary prevInSummary, RhoSigmaEscapeMap out, SootMethod targetMethod, Value actualThisVar,Value formalThisVar) {

		String actualThisVarName = className+"_"+methodName+"_"+actualThisVar.toString(); 
		String formalThisVarName = targetMethod.getDeclaringClass().toString()+"_"+targetMethod.getName()+"_"+formalThisVar.toString(); 

		
		//union of rho of 'this' var
		if(prevInSummary.stack.containsKey(formalThisVarName)){
			
			if(out.stack.containsKey(actualThisVarName))
				prevInSummary.stack.get(formalThisVarName).addAll(out.stack.get(actualThisVarName));
		}else{
			if(out.stack.containsKey(actualThisVarName))
				prevInSummary.stack.put(formalThisVarName, out.stack.get(actualThisVarName));
		}

		//union of sigma of 'this' var
		if(out.stack.containsKey(actualThisVarName)){
			for(String obj: out.stack.get(actualThisVarName)){
				
				if(prevInSummary.heap.containsKey(obj)) {
					for(Entry<String,Set<String>> fieldEntry: prevInSummary.heap.get(obj).entrySet()){
						String field = fieldEntry.getKey();

						if(prevInSummary.heap.get(obj).containsKey(field)) {
							prevInSummary.heap.get(obj).get(field).addAll(out.heap.get(obj).get(field));
						}else {
							prevInSummary.heap.get(obj).put(field, new HashSet<>(out.heap.get(obj).get(field)));
						}
					}
				}else {
					if(out.heap.containsKey(obj))
						prevInSummary.heap.put(obj, new HashMap<>(out.heap.get(obj)));
				}
				
			}
		}
		
		//union of escapemap 
		prevInSummary.escapeMap.addAll(out.escapeMap);
				
	}
	void unionOfOutSummary(RhoSigmaEscapeMap out, OutSummary outSummary, Value baseVar) {
		
		
		String baseVarName = className + "_" + methodName + "_" + baseVar.toString();

		for(Entry<String,Map<String,Set<String>>> objEntry: outSummary.heap.entrySet()) {
			String obj = objEntry.getKey();
			if(out.heap.containsKey(obj)) {
				for(Entry<String,Set<String>> fieldEntry: objEntry.getValue().entrySet()) {
					String field = fieldEntry.getKey();
					if(out.heap.get(obj).containsKey(field)) {
						out.heap.get(obj).get(field).addAll(outSummary.heap.get(obj).get(field));
					}else {
						out.heap.get(obj).put(field, outSummary.heap.get(obj).get(field));
					}
				}
			}else {
				out.heap.put(obj, new HashMap<>(outSummary.heap.get(obj)));
			}
		}		
		out.escapeMap.addAll(outSummary.escapeMap);
	}
	
	boolean isSameOutSummary(OutSummary prevOutSummary, RhoSigmaEscapeMap out){
		
		if(prevOutSummary.heap.equals(out.heap)) {
			if(prevOutSummary.escapeMap.equals(out.escapeMap))
				return true;
		}
		return false;
	}
	
	public boolean isInSummarySame(RhoSigmaEscapeMap curr, SootMethod targetMethod, InSummary prevInSummary, Value actualThisVar, Value formalThisVar) {
		String actualThisVarName = className+"_"+methodName+"_"+actualThisVar.toString(); 
		String formalThisVarName = targetMethod.getDeclaringClass().toString()+"_"+targetMethod.getName()+"_"+formalThisVar.toString(); 

		if(prevInSummary.stack.containsKey(formalThisVarName)){
			//check rho of this var
			if(prevInSummary.stack.get(formalThisVarName).equals(curr.stack.get(actualThisVarName))) {
				//check escape map
				if(prevInSummary.escapeMap.equals(curr.escapeMap)) {
					
					//check sigma of this var
					for(String obj: prevInSummary.stack.get(formalThisVarName)) {
						if(prevInSummary.heap.containsKey(obj)) {
							if(prevInSummary.heap.get(obj).equals(curr.heap.get(obj))) {
								return false;
							}
						}else {
							if(curr.heap.containsKey(obj))
								return false;
						}
							
					}
				}else
					return false;
				
			}else 
				return false;
		}else {
			if(curr.stack.containsKey(actualThisVarName))
				return false;
		}
		
		return true;
	}
	
	
	//get all reachable objects
	public Set<String> reachable(String var, RhoSigmaEscapeMap in){
		Set<String> visited = new HashSet<>();
		Queue<String> q = new LinkedList<>();
		Set<String> reachableSet = new HashSet<>();
		
		if(!in.stack.containsKey(var)) {
			return reachableSet;
		}
		for(String ref: in.stack.get(var)) {
			q.add(ref);
			visited.add(ref);
			reachableSet.add(ref);
		}
		
		while(!q.isEmpty()){
			String obj = q.poll();
			if(in.heap.containsKey(obj)){
				for(Entry<String,Set<String>> entry: in.heap.get(obj).entrySet()) {
					String field = entry.getKey();
					for(String fieldRef: entry.getValue()) {
						if(!visited.contains(fieldRef)) {
							q.add(fieldRef);
							visited.add(fieldRef);
						}
						if(!reachableSet.contains(fieldRef))
							reachableSet.add(fieldRef);
					}
				}
			}
		}
		return reachableSet;
	}
	
	
	//Creates deep copy of object of type DS
	public RhoSigmaEscapeMap copyObject(RhoSigmaEscapeMap rs) {
		RhoSigmaEscapeMap copy = new RhoSigmaEscapeMap();
		if(!rs.stack.isEmpty()) {
			
			for(Entry<String, Set<String>> entry: rs.stack.entrySet()){
				String var = entry.getKey();
				copy.stack.put(var, new HashSet<>(entry.getValue()));
			}
		}
		if(!rs.heap.isEmpty()) {
			for (Entry<String,Map<String,Set<String>>> entry : rs.heap.entrySet()) {
				String objName = entry.getKey();
				Map<String,Set<String>> newMap = new HashMap<>();
				for (Entry<String,Set<String>> fieldEntry : rs.heap.get(objName).entrySet()){
		    		String fieldName = fieldEntry.getKey();
		    		newMap.put(fieldName, new HashSet<>(fieldEntry.getValue()));
				}
	    		copy.heap.put(objName, newMap);	
			}
		}
		
		//need to validate this
		copy.escapeMap.addAll(rs.escapeMap);
		
		return copy;
	}
			
	//union of two DS
	void unionOfPred(RhoSigmaEscapeMap union, RhoSigmaEscapeMap outPred){
		
		//union of stack
		for(Entry<String, Set<String>> entry: outPred.stack.entrySet()){
			String var = entry.getKey();
			if(union.stack.containsKey(var)) {
				union.stack.get(var).addAll(entry.getValue());
			}else {
				union.stack.put(var, entry.getValue());
			}
		}
		
		//union of sigma
		for(Entry<String, Map<String,Set<String>>> refEntry: outPred.heap.entrySet()){
			
			String ref = refEntry.getKey();
			Map<String,Set<String>> mapOfFields = refEntry.getValue();
			if(union.heap.containsKey(ref)){
				for(Entry<String,Set<String>> fieldEntry: mapOfFields.entrySet()){
					String field = fieldEntry.getKey();
					if(union.heap.get(ref).containsKey(field)) {
						union.heap.get(ref).get(field).addAll(fieldEntry.getValue());
					}else {
						union.heap.get(ref).put(field, new HashSet<>(fieldEntry.getValue()));
					}
				}
			}else {
				Map<String,Set<String>> newMapOfFields = new HashMap<>();
				for(Entry<String,Set<String>> fieldEntry: mapOfFields.entrySet()){
					String field = fieldEntry.getKey();
					newMapOfFields.put(field, new HashSet<>(fieldEntry.getValue()));
				}
				union.heap.put(ref, newMapOfFields);
			}
		}
		
		//union of escape map
		union.escapeMap.addAll(outPred.escapeMap);
		
	}
	
	
//returns true if two rho -> Set<String> are equal
	public synchronized boolean checkRho(RhoSigmaEscapeMap prev, RhoSigmaEscapeMap curr) {
		
		//check stack
		if(prev.stack.equals(curr.stack))
			return true;
		return false;
		
	}
	
	//returns true if two sigma -> Map<x,Map<field,Set<Ref>>> are equal
	public synchronized boolean checkSigma(RhoSigmaEscapeMap prev, RhoSigmaEscapeMap curr) {
		
		if(prev.heap.equals(curr.heap))
			return true;
		return false;
		
	}
	
	public synchronized boolean checkEscapeMap(RhoSigmaEscapeMap prev, RhoSigmaEscapeMap curr) {
		if(prev.escapeMap.equals(curr.escapeMap))
			return true;
		return false;
	}

	
	//return true if two data structures RhoSigma are equal
	public synchronized boolean isSame(RhoSigmaEscapeMap prev, RhoSigmaEscapeMap curr) {
		
		if(!(checkRho(prev,curr) && checkSigma(prev,curr) && checkEscapeMap(prev,curr)))
			return false;
	
		return true;
	}

	
	//add fields of all super classes of obj
	public synchronized Map<String, Set<String>> getSuperClassFields(Value rhs){
		
		SootClass objClass = ((NewExpr) rhs).getBaseType().getSootClass();
		Map<String, Set<String>> newMap = new HashMap<>();
		if(allClassesInProgram.contains(objClass)) {
			
			//add all fields of new obj
			Chain<SootField> chain= objClass.getFields();
			
			for(SootField field: chain) {
				newMap.put(field.getName(),new HashSet<>());	
			}
		}
		while(objClass.hasSuperclass()) {
			if(allClassesInProgram.contains(objClass.getSuperclass())) {
				Chain<SootField> superChain = objClass.getSuperclass().getFields();
				for(SootField superField: superChain){
					newMap.put(superField.getName(),new HashSet<>());
				}
			
			}
			objClass = objClass.getSuperclass();	
		}
		return newMap;
	}
	
//	public synchronized void print(RhoSigmaEscapeMap out) {
//		System.out.println("RHO");
//		out.stack.entrySet().forEach(entry -> {
//		    System.out.println(entry.getKey() + " " + entry.getValue());
//		});
//		
//		System.out.println("SIGMAA");
//		out.heap.entrySet().forEach(entry -> {
//		    System.out.println(entry.getKey() + " " + entry.getValue());
//		});
//		System.out.println("ESCAPE MAP");
//		System.out.println(out.escapeMap); 
//		
//	}
}
