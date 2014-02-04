package submit;

// some useful things to import. add any additional imports you need.
import joeq.Compiler.Quad.*;
import flow.Flow;
import java.util.Iterator;
/**
 * Skeleton class for implementing the Flow.Solver interface.
 */
public class MySolver implements Flow.Solver {

    protected Flow.Analysis analysis;

    /**
     * Sets the analysis.  When visitCFG is called, it will
     * perform this analysis on a given CFG.
     *
     * @param analyzer The analysis to run
     */
    public void registerAnalysis(Flow.Analysis analyzer) {
        this.analysis = analyzer;
    }

    /**
     * Runs the solver over a given control flow graph.  Prior
     * to calling this, an analysis must be registered using
     * registerAnalysis
     *
     * @param cfg The control flow graph to analyze.
     */
    public void visitCFG(ControlFlowGraph cfg) {

        analysis.preprocess(cfg);

        System.out.println("Visit CFG.");

        if (this.analysis.isForward()){
            System.out.println("Forward dataflow.");
            boolean outChanged = false;
            int it =0;   // debug counter
            do {
                System.out.format("Iteration %d\n",it); it++;
                outChanged = forwardFlow(cfg);
            }while(outChanged);
        }else{
            System.out.println("Backward dataflow.");
            boolean inChanged = false;
            do {
                inChanged = backwardFlow(cfg);
            }while(inChanged);
        }
        analysis.postprocess(cfg);
    }
    
    /** 
     * Forward data-flow solver
     1)  compute IN of block using meet operator
     2)  compute OUT of block using IN and transfer
     3)  repeat until converge
         
     - for each curQuad  in the cfg iterator
     - get predeccessors of curQuad
     - if we are a predecessor of an exit, add curQuad to exitPred.
     - perform transfer function
     - gather all quad in the exit: exitPred
     - process the exit

     * @param cfg The control flow graph to analyze.
     */
    private boolean forwardFlow(ControlFlowGraph cfg){

        boolean outChanged =false;
        QuadIterator iter = new QuadIterator(cfg, true);

        int i = 0; // debug counter

        while(iter.hasNext()){

            System.out.format("Basic block %d\n", i );
            i++;

            /* get predecessors of current quad */
            Quad currentQuad = (Quad)iter.next();

            // old OUT value used for comparison
            Flow.DataflowObject oldOut=this.analysis.getOut(currentQuad);

            // variable to hold the new IN
            Flow.DataflowObject meetResult = this.analysis.newTempVar();

                
            /* meet with the OUTs of all predecessors to compute IN */

            Iterator<Quad> predIter = iter.predecessors(); 
            if (predIter  == null){
                meetResult.meetWith(this.analysis.getEntry());
            }else{
                    
                while(predIter.hasNext()){
                    Quad prevQuad =  (Quad)predIter.next();
                    if (prevQuad !=null){
                        meetResult.meetWith(this.analysis.getOut(prevQuad));
                    }else{
                        meetResult.meetWith(this.analysis.getEntry());
                    }
                }
            }
            this.analysis.setIn(currentQuad,meetResult);

            /* compute OUT using transfer function */
            this.analysis.processQuad(currentQuad);
            Flow.DataflowObject lastOut = this.analysis.getOut(currentQuad);
            this.analysis.setExit(lastOut);

            /* check changes to OUT */
            if (!oldOut.equals(lastOut)){
                outChanged = true;
            }

        }
        return outChanged;
    }


    /** 
     * Forward data-flow solver
     * @param cfg The control flow graph to analyze.
     */
    private boolean backwardFlow(ControlFlowGraph cfg){
        boolean inChanged =false;
        QuadIterator iter = new QuadIterator(cfg, false);

        int i = 0; // debug counter

        while(iter.hasPrevious()){

            System.out.format("Basic block %d\n", i );
            i++;

            // get predecessors of current quad 
            Quad currentQuad = (Quad)iter.previous();

            // old IN value used for comparison
            Flow.DataflowObject oldIn=this.analysis.getIn(currentQuad);

            // variable to hold the new IN
            Flow.DataflowObject meetResult = this.analysis.newTempVar();

                
            // meet with the INs of all predecessors to compute OUT 

            Iterator<Quad> succIter = iter.successors(); 
            if (succIter  == null){
                meetResult.meetWith(this.analysis.getExit());
            }else{
                    
                while(succIter.hasNext()){

                    Quad succQuad =  (Quad)succIter.next();
                    if (succQuad !=null){
                        meetResult.meetWith(this.analysis.getIn(succQuad));
                    }else{
                        meetResult.meetWith(this.analysis.getExit());
                    }
                }
            }
            this.analysis.setOut(currentQuad,meetResult);

            // compute IN using transfer function 
            this.analysis.processQuad(currentQuad);
            Flow.DataflowObject lastIn = analysis.getIn(currentQuad);
            this.analysis.setEntry(lastIn);

            // check changes to IN
            if (!oldIn.equals(lastIn)){
                // !!! instruction below causes infinite loop 
                inChanged = true;
            }

        }
        return inChanged;
    }
}
  