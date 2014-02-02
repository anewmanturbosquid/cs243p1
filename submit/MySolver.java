package submit;

// some useful things to import. add any additional imports you need.
import joeq.Compiler.Quad.*;
import flow.Flow;

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

        // this needs to come first.
        analysis.preprocess(cfg);

            System.out.println("Visit CFG.");
        /***********************
         * Your code goes here *
         1)  compute IN of block using meet operator
         2)  compute OUT of block using IN and transfer
         3)  repeat until converge
         ***********************/
        if (this.analysis.isForward()){
            System.out.println("Forward dataflow.");
            boolean outChanged = false;
            
            
              
            /* iterative alg for a forward data flow */
            do{
                outChanged =false;
                QuadIterator iter = new QuadIterator(cfg, true);
                while(iter.hasNext()){

                    /* meet with the OUTs of all predecessors to compute IN */

                    java.util.Iterator<Quad> preds = iter.predecessors();

                    Quad currentQuad = (Quad)iter.next();
                    Flow.DataflowObject oldOut = this.analysis.getOut(currentQuad);
                    Flow.DataflowObject meetResult = this.analysis.newTempVar();

                    while(preds.hasNext()){
                        Quad prevQuad =  (Quad)preds.next();
                        meetResult.meetWith(this.analysis.getOut(prevQuad));
                    }
                    this.analysis.setIn(currentQuad,meetResult);

                    /* compute OUT using transfer function */

                    this.analysis.processQuad(currentQuad);

                    /* check changes to OUT */
                    if (oldOut != this.analysis.getOut(currentQuad)){
                        outChanged = true;
                    }


                    
                    
                }

                /* check whether any OUT changed */


            }while(outChanged);


        }else{
            System.out.println("Backward dataflow.");
        }
        

        // this needs to come last.
        analysis.postprocess(cfg);
    }
}
