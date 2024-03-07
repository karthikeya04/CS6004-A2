import java.util.Iterator;
import java.util.List;
import java.util.TreeMap;
import soot.*;
import soot.jimple.internal.*;
import soot.toolkits.graph.ExceptionalUnitGraph;
import soot.toolkits.graph.UnitGraph;

public class PA2 {
    public static void main(String[] args) {
        String classPath = "."; // change to appropriate path to the test class
        String dir = "./testcase";
        // Set up arguments for Soot
        String[] sootArgs = {"-cp", classPath, "-pp",
            "-print-tags", // sets the class path for Soot
            "-keep-line-number", // preserves line numbers in input Java
                                 // files
            "-f", "J", "-main-class", "Test", // specify the main class
            // "Test", "Node" // list the classes to analyze
            "-process-dir", dir};

        // Create transformer for analysis
        AnalysisTransformer analysisTransformer = new AnalysisTransformer();

        // Add transformer to appropriate pack in PackManager; PackManager will
        // run all packs when soot.Main.main is called
        PackManager.v().getPack("jtp").add(
            new Transform("jtp.dfa", analysisTransformer));

        // Call Soot's main method with arguments
        soot.Main.main(sootArgs);

        TreeMap<String, List<Integer>> result = AnalysisTransformer.result;
        for (String key : result.keySet()) {
            if (result.get(key).size() == 0)
                continue;
            String objectsStr = result.get(key).toString();
            objectsStr = objectsStr
                             .replace(",", "") // remove the commas
                             .replace("[", "") // remove the right bracket
                             .replace("]", "") // remove the left bracket
                             .trim();
            System.out.println(key + " " + objectsStr);
        }
    }
}
