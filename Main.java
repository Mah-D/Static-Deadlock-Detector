/**************************************************************************
 * @author Mahdi Eslamimehr
 * @version 0.1
 ***************************************************************************/


package ContractGen;

import java.util.*;
import soot.Body;
import soot.NormalUnitPrinter;
import soot.Scene;
import soot.SootClass;
import soot.SootMethod;
import soot.Unit;
import soot.UnitPrinter;
import soot.toolkits.graph.ExceptionalUnitGraph;
import soot.toolkits.graph.BriefUnitGraph;
import soot.toolkits.graph.UnitGraph;
import soot.jimple.*;
import soot.jimple.toolkits.callgraph.*;
import soot.Value;
import soot.toolkits.graph.*;
import soot.SootMethod;
import soot.util.queue.QueueReader;
import soot.util.*;
import soot.jimple.paddle.*;

public class Main {
    // Verbosity options, primarily for debugging

    private static HashMap opt;
    public static int count = 0;
    public static String ustring = "java ContractGen <verbosity level (verbose0/verbose1/verbose2/verbose3)>\n"+
                                   "                 <library-prefix> (e.g. java.lang)\n"+
                                   "                 <list-of-classes-to-be-analyzed> \n"+
                                   "                 <directory-to-hold-constraints\n";

    static {
        soot.options.Options.v().set_keep_line_number(true);
        soot.options.Options.v().set_whole_program(true);
        soot.options.Options.v().setPhaseOption("cg","verbose:false");
        opt = new HashMap();
        opt.put("useRecursiveFP", "true");
        opt.put("useTypeAliasing", "true");
        opt.put("avoidLocals", "false");
        opt.put("useSpark", "false");
        opt.put("partitionLG", "true");
    }

    /***************************************************************
     * Required Arguments:
     *       arg[0] : verbosity level
     *       arg[1] : top-level-lib-prefix
     *       arg[2] : list of classes to be analyzed
     *       arg[3] : output dir
     ***************************************************************/    
    
    public static void main(String[] args) {
        // Some settings for debugging
        Runtime r = Runtime.getRuntime();
        r.traceMethodCalls(true);
        E.name("ContractGen");
        if (args.length!=4) E.usage(ustring);
        if (!args[0].startsWith("verbose")) E.usage(ustring);
        int e = args[0].lastIndexOf('e');
        int verbLevel = Integer.parseInt(args[0].substring(e+1));
        if (verbLevel<0 || verbLevel>3) E.usage(ustring);
        opt.put("verboseLG",       ((verbLevel>1)?"true":"false"));
        opt.put("verboseLGSub",    ((verbLevel>2)?"true":"false"));
        opt.put("verboseIntraP",   ((verbLevel>1)?"true":"false"));
        opt.put("verboseCGInfo",   ((verbLevel>2)?"true":"false"));
        opt.put("verboseAnalysis", ((verbLevel>1)?"true":"false"));
        opt.put("verboseConstGen", ((verbLevel>0)?"true":"false"));
        opt.put("verbosePatGen",   ((verbLevel>2)?"true":"false"));
        opt.put("verboseSyn",      ((verbLevel>1)?"true":"false"));

        E.setOptions(opt);
        Analyzer A = new Analyzer(args[2], args[3]);
        A.addUnskippable(args[1]);
        A.doAnalysis();
    }
}

