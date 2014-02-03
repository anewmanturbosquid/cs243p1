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
            
            
            int it =0;   // debug counter
            /* iterative alg for a forward data flow */
            do{
                System.out.format("Iteration %d\n",it); it++;
                outChanged =false;
                QuadIterator iter = new QuadIterator(cfg, true);

                int i = 0; // debug counter

                while(iter.hasNext()){

                    /* meet with the OUTs of all predecessors to compute IN */
                    System.out.format("Basic block %d\n", i );
                    i++;
                    if (!iter.hasPrevious()){
                        iter.next();
                        continue;
                    }
                    iter.predecessors();

                    java.util.Iterator<Quad> preds = iter.predecessors();
                    Quad currentQuad = (Quad)iter.next();
                    Flow.DataflowObject oldOut = this.analysis.getOut(currentQuad)
                    Flow.DataflowObject meetResult = this.analysis.newTempVar();

                    while(preds.hasNext()){
                        Quad prevQuad =  (Quad)preds.next();
                        if (prevQuad !=null){
                            meetResult.meetWith(this.analysis.getOut(prevQuad));
                        }
                    }
                    this.analysis.setIn(currentQuad,meetResult);

                    /* compute OUT using transfer function */
                    this.analysis.processQuad(currentQuad);

                    /* check changes to OUT */
                    if (oldOut != this.analysis.getOut(currentQuad)){
                        /* !!! instruction below causes infinite loop */
                           outChanged = true;
                    }
                }

            }while(outChanged);


        }else{
            System.out.println("Backward dataflow.");
            boolean inChanged = false;

            /* iterative alg for a forward data flow */
            do{
                inChanged =false;
                QuadIterator iter = new QuadIterator(cfg,false);

                while(iter.hasNext()){
                    /* meet with the INs of all successors of compute OUT
                    */

                    if (iter.successors() == null){
                        iter.next();
                        continue;
                    }
                    iter.successors();

                    java.util.Iterator<Quad> preds = iter.predecessors();
                    Quad currentQuad = (Quad)iter.next();
                    Flow.DataflowObject oldOut = this.analysis.getOut(currentQuad)
                    Flow.DataflowObject meetResult = this.analysis.newTempVar();

                    while(preds.hasNext()){
                        Quad prevQuad =  (Quad)preds.next();
                        if (prevQuad !=null){
                            meetResult.meetWith(this.analysis.getOut(prevQuad));
                        }
                    }
                    this.analysis.setIn(currentQuad,meetResult);

                    /* compute OUT using transfer function */
                    this.analysis.processQuad(currentQuad);

                    /* check changes to OUT */
                    if (oldOut != this.analysis.getOut(currentQuad)){
                        /* !!! instruction below causes infinite loop */
                           outChanged = true;
                    }
                }

            }while(outChanged);

        }
        

        // this needs to come last.
        analysis.postprocess(cfg);
    }
}
