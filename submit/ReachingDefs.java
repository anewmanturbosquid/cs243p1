
package submit;

// some useful things to import. add any additional imports you need.
import java.util.ArrayList;
import java.util.HashSet;
import java.util.Iterator;
import java.util.List;
import java.util.Map;
import java.util.Map.Entry;
import java.util.Set;
import java.util.TreeMap;

import joeq.Compiler.Quad.ControlFlowGraph;
import joeq.Compiler.Quad.Operand.RegisterOperand;
import joeq.Compiler.Quad.Quad;
import joeq.Compiler.Quad.QuadIterator;
import flow.Flow;

/**
 * Skeleton class for implementing a reaching definition analysis
 * using the Flow.Analysis interface.
 */
public class ReachingDefs implements Flow.Analysis {

    /**
     * Class for the dataflow objects in the ReachingDefs analysis.
     * You are free to change this class or move it to another file.
     */
    public class MyDataflowObject implements Flow.DataflowObject {
        /**
         * Methods from the Flow.DataflowObject interface.
         * See Flow.java for the meaning of these methods.
         * These need to be filled in.
         */

    	// Use * SortedSets and SortedMaps instead of the normal kinds.
        Map<Integer,String> sortedMap = new TreeMap<Integer,String>();

        public MyDataflowObject()
        {
        	this.initSortedMap();
        }

        public void initSortedMap()
        {
        	this.sortedMap = new TreeMap<Integer,String>();
        }
        
        public void setToTop() 
        {
        	this.initSortedMap();

        }

        public void setToBottom() 
        {
        	this.initSortedMap();

        }


        public void meetWith (Flow.DataflowObject o) 
        {
            MyDataflowObject curObject = (MyDataflowObject) o;
            
//            HashSet<Integer> keySet = (HashSet<Integer>) curObject.sortedMap.keySet();
            Set<Integer> keySet = curObject.sortedMap.keySet();
            
            for (int key : keySet)
            {
            	this.sortedMap.put(key, curObject.sortedMap.get(key));
            }
            	

        }


//        public void addAll(Flow.DataflowObject o)
//        {
//        	
//        }
        
        public void copy (Flow.DataflowObject object) 
        {
            MyDataflowObject curObject = (MyDataflowObject) object;
            
            this.sortedMap = new TreeMap<Integer,String>(curObject.sortedMap);
            
        }
        


        /**
         * toString() method for the dataflow objects which is used
         * by postprocess() below.  The format of this method must
         * be of the form "[ID0, ID1, ID2, ...]", where each ID is
         * the identifier of a quad defining some register, and the
         * list of IDs must be sorted.  See src/test/test.rd.out
         * for example output of the analysis.  The output format of
         * your reaching definitions analysis must match this exactly.
         */
        @Override
        public String toString() 
        { 
        	return this.sortedMap.keySet().toString(); 
        }
        
        public void gen(String s, int id)
        {
        	this.sortedMap.put(id, s);
        }
        
        public void kill(String s)
        {
        	//invert, remove, invert again--don't care about duplicates, bc it's getting removed anyway
        	
//        	Map<String,Integer> tempMap = this.invertMap(this.sortedMap);
//        	
//        	tempMap.remove(s);
//        	
//        	this.sortedMap = this.invertMap(tempMap);

        	List<Integer> keys = getKey(s, this.sortedMap);
        	
        	this.sortedMap.keySet().removeAll(keys);
        	

        }
        
//        //adapted from http://stackoverflow.com/questions/7146990/java-invert-map
//        private <V, K> Map<V, K> invertMap(Map<K, V> map) {
//
//            Map<V, K> inv = new TreeMap<V, K>();
//
//            for (Entry<K, V> entry : map.entrySet())
//                inv.put(entry.getValue(), entry.getKey());
//
//            return inv;
//        }
        
        //from http://stackoverflow.com/questions/11795777/how-to-get-key-depending-upon-the-value-from-hashmap
        /**
         * Return keys associated with the specified value
         */
        public List<Integer> getKey(String value, Map<Integer, String> map) {
          List<Integer> keys = new ArrayList<Integer>();
          for(Entry<Integer, String> entry:map.entrySet()) {
            if(value.equals(entry.getValue())) {
              keys.add(entry.getKey());
            }
          }
          return keys;
        }
        
        public boolean equals(Object object)
        {

            MyDataflowObject castedobj = (MyDataflowObject) object;
            
            if (this.sortedMap.equals(castedobj.sortedMap))
            	return true;
            else 	
            	return false;
            
            
        }
        
        
        public int hashCode() 
        {
        	
            return this.sortedMap.hashCode();
            
        }
        
    }
    
    

    /**
     * Dataflow objects for the interior and entry/exit points
     * of the CFG. in[ID] and out[ID] store the entry and exit
     * state for the input and output of the quad with identifier ID.
     *
     * You are free to modify these fields, just make sure to
     * preserve the data printed by postprocess(), which relies on these.
     */
    private MyDataflowObject[] in, out;
    private MyDataflowObject entry, exit;
    
    private ArrayList<Integer> exitBlocks;

    /**
     * This method initializes the datflow framework.
     *
     * @param cfg  The control flow graph we are going to process.
     */
    public void preprocess(ControlFlowGraph cfg) {
        // this line must come first.
        System.out.println("Method: "+cfg.getMethod().getName().toString());

        // get the amount of space we need to allocate for the in/out arrays.
        QuadIterator qit = new QuadIterator(cfg);
        int max = 0;
        while (qit.hasNext()) {
            int id = qit.next().getID();
            if (id > max) 
                max = id;
        }
        max += 1;

        // allocate the in and out arrays.
        in = new MyDataflowObject[max];
        out = new MyDataflowObject[max];

        // initialize the contents of in and out.
        qit = new QuadIterator(cfg);
        while (qit.hasNext()) {
            int id = qit.next().getID();
            in[id] = new MyDataflowObject();
            out[id] = new MyDataflowObject();
        }

        // initialize the entry and exit points.
        entry = new MyDataflowObject();
        exit = new MyDataflowObject();

        /************************************************
         * Your remaining initialization code goes here *
         ************************************************/
        
        this.exitBlocks = new ArrayList<Integer>();
        
        //find blocks that exit
        
        int i=1;
        QuadIterator newIter = new QuadIterator(cfg);
//        newIter.next();
        

        
        while (newIter.hasNext()) 
        {
        	Quad curQuad = newIter.next();
        	Iterator<Quad> successors = newIter.successors();

//        	System.out.println(i);
        	
        	HashSet<Quad> curSuccSet = new HashSet<Quad>();
        	
        	while (successors.hasNext())
        		curSuccSet.add(successors.next());
        	
        	if (curSuccSet.contains(null))
//        		System.out.println(i);
        		this.exitBlocks.add(curQuad.getID());
        	
        	
        	i+=1;
        }
//        System.out.println("hi");
    }

    /**
     * This method is called after the fixpoint is reached.
     * It must print out the dataflow objects associated with
     * the entry, exit, and all interior points of the CFG.
     * Unless you modify in, out, entry, or exit you shouldn't
     * need to change this method.
     *
     * @param cfg  Unused.
     */
    public void postprocess (ControlFlowGraph cfg) {
        System.out.println("entry: " + entry.toString());
        for (int i=0; i<in.length; i++) {
            if (in[i] != null) {
                System.out.println(i + " in:  " + in[i].toString());
                System.out.println(i + " out: " + out[i].toString());
            }
        }
        System.out.println("exit: " + exit.toString());
    }

    /**
     * Other methods from the Flow.Analysis interface.
     * See Flow.java for the meaning of these methods.
     * These need to be filled in.
     */
    public boolean isForward () { return true; }
    
    
    //mostly taken from corresponding code in ConstantProp.java
    
    
    public Flow.DataflowObject getEntry() 
    { 
        Flow.DataflowObject result = newTempVar();
        result.copy(this.entry); 
        return result;
        
//        return this.entry;
    }
    public Flow.DataflowObject getExit()
    { 
        Flow.DataflowObject result = newTempVar();
        result.copy(this.exit); 
        return result;
        
    }
    
    public void setEntry(Flow.DataflowObject value)
    {
    	this.entry.copy(value);
    }
    public void setExit(Flow.DataflowObject value)
    {
//    	this.exit.copy(value);
    	
        Flow.DataflowObject result = newTempVar();
        result.copy(this.exit); 
        
//        System.out.println(this.exitBlocks);

    	
    	for (int curInt : this.exitBlocks)
    	{
//    		System.out.println(curInt);
    		result.meetWith(out[curInt]);
    	}
    	
    	this.exit.copy(result);
    	
//    	System.out.println("hi");
//    	this.exit.meetWith(value);
    }
    
    public Flow.DataflowObject getIn(Quad q) { 
        Flow.DataflowObject result = newTempVar();
        result.copy(in[q.getID()]); 
        return result;
    }
    public Flow.DataflowObject getOut(Quad q) { 
        Flow.DataflowObject result = newTempVar();
        result.copy(out[q.getID()]); 
        return result;
    }
    
    public void setIn(Quad q, Flow.DataflowObject value) 
    { 
        this.in[q.getID()].copy(value); 
    }
    public void setOut(Quad q, Flow.DataflowObject value)
    { 
        this.out[q.getID()].copy(value); 
    }
    
    public Flow.DataflowObject newTempVar()
    { 
    	MyDataflowObject curObj = new MyDataflowObject();
    	return curObj; 
    }
    
    public void processQuad(Quad q)
    {
    	MyDataflowObject curObj = new MyDataflowObject ();
    	
    	
    	curObj.copy(in[q.getID()]);
    	
    	//q.getUsedRegisters()
    	
        for (RegisterOperand tempDefinedRegister : q.getDefinedRegisters()) 
        	curObj.kill(tempDefinedRegister.getRegister().toString());
      
        for (RegisterOperand tempDefinedRegister : q.getDefinedRegisters()) 
        	curObj.gen(tempDefinedRegister.getRegister().toString(), q.getID());
        
        
//        System.out.println(q.getID());
        
//        System.out.println(q.getDefinedRegisters());
//        System.out.println(q.getUsedRegisters());
        
//        Helper.runPass(q, transferfn);
        
        
        out[q.getID()].copy(curObj);
    	
    	
    }
    
}