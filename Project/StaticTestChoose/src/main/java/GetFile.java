import com.ibm.wala.classLoader.ShrikeBTMethod;
import com.ibm.wala.ipa.callgraph.AnalysisScope;
import com.ibm.wala.ipa.callgraph.CGNode;
import com.ibm.wala.ipa.callgraph.CallGraph;
import com.ibm.wala.ipa.callgraph.Entrypoint;
import com.ibm.wala.ipa.callgraph.cha.CHACallGraph;
import com.ibm.wala.ipa.callgraph.impl.AllApplicationEntrypoints;
import com.ibm.wala.ipa.cha.ClassHierarchy;
import com.ibm.wala.ipa.cha.ClassHierarchyException;
import com.ibm.wala.ipa.cha.ClassHierarchyFactory;
import com.ibm.wala.shrikeCT.InvalidClassFileException;
import com.ibm.wala.types.ClassLoaderReference;
import com.ibm.wala.types.annotations.Annotation;
import com.ibm.wala.util.CancelException;
import com.ibm.wala.util.config.AnalysisScopeReader;

import java.io.*;
import java.util.*;

/**
 * @author Yang ShengYuan
 * @date 2020/11/13
 * @Description xxx
 **/
public class GetFile {
    public static void main(String[] args){
        String selectType = args[0];
        String projectTargetPath = args[1];
        String changeInfoPath = args[2];
//        String scopePath = "src/main/resources/scope.txt";
//        String exclusionPath = "src/main/resources/exclusion.txt";
        String scopePath = "scope.txt";
        String exclusionPath = "exclusion.txt";

        try {
            execute(selectType,projectTargetPath,changeInfoPath,scopePath,exclusionPath);
        } catch (CancelException e) {
            e.printStackTrace();
        } catch (ClassHierarchyException e) {
            e.printStackTrace();
        } catch (InvalidClassFileException e) {
            e.printStackTrace();
        } catch (IOException e) {
            e.printStackTrace();
        }

    }

    public static void execute(String selectType, String projectTargetPath, String changeInfoPath,String scopePath, String exclusionPath) throws CancelException, ClassHierarchyException, InvalidClassFileException, IOException {
        CallGraph cg = getCallGraph(projectTargetPath,scopePath,exclusionPath);
        //获取changeInfo文件内容
        ArrayList<String> changeInfo = getChangedInfo(changeInfoPath,selectType);
        //类名和方法名列表(L+包名形式)，方法名中包括类名
        HashSet<String> classes = new HashSet<String>();
        HashSet<String> methods = new HashSet<String>();
        HashSet<String> testMethods = new HashSet<String>();
        //遍历node
        getCallGraphInfo(cg, classes,methods,testMethods);
        int[][] adjacencyMatrix;
        HashMap<Integer,String> index = new HashMap<Integer, String>();
        HashMap<String,Integer> indexReverse = new HashMap<String,Integer>();
        int matrixCount = 0;
        if(selectType.equals("-c")){
            matrixCount = classes.size();
            setMatrixIndex(index,indexReverse,classes);
        }else if(selectType.equals("-m")){
            matrixCount = methods.size();
            setMatrixIndex(index,indexReverse,methods);
        }
        adjacencyMatrix = new int[matrixCount][matrixCount];
        //继续遍历node填充邻接矩阵
        HashSet<String> dependencyTemp = new HashSet<String>();
        getDependencyInfo(cg,adjacencyMatrix,dependencyTemp,methods,selectType,indexReverse);
//       根据是类级还是方法级的测试用例选择来在邻接矩阵上选择受影响的测试用例
        //在矩阵上运算
        ComputeTransitiveClosure(adjacencyMatrix);
        HashSet<String> selectedMethods = new HashSet<String>();
        if(selectType.equals("-c")) {
            //类级
            //根据被修改的类名找到所有相关的类,string为L+包的形式
            HashSet<String> influencedClasses = new HashSet<String>();
            for(String changedClass: changeInfo){
                int i = indexReverse.get(changedClass);
                for(int k = 0; k<adjacencyMatrix.length;k++){
                    if(adjacencyMatrix[i][k]==1){
                        String influencedClass = index.get(k);
                        influencedClasses.add(influencedClass);
                    }
                }
            }
            //遍历一遍方法找到测试类中的方法
            for(String method: testMethods){
                if(influencedClasses.contains(method.split(" ")[0])){
                    selectedMethods.add(method);
                }
            }
        }else if(selectType.equals("-m")) {
            //方法级
            // 找到和更改方法相关的方法,String为signature
            for(String changedMethod: changeInfo){
                int i = indexReverse.get(changedMethod);
                for(int k = 0; k<adjacencyMatrix.length;k++){
                    if(adjacencyMatrix[i][k]==1){
                        String influencedMethod = index.get(k);
                        //筛选出类名是在测试类名中的方法
                        if(testMethods.contains(influencedMethod)){
                            selectedMethods.add(influencedMethod);
                        }
                    }
                }
            }
        }

//        输出结果到指定文件中
        if(selectType.equals("-c")){
            outputSelectedMethod("selection-class.txt",selectedMethods);
//            outputDependencies("class-CMD.text",dependencyTemp);
        }else if(selectType.equals("-m")){
            outputSelectedMethod("selection-method.txt",selectedMethods);
//            outputDependencies("method-CMD.text",dependencyTemp);
        }
    }

    public static void getFileInDic(File file,ArrayList<String> fileNames){
        String fileName = file.getName();
        if(fileName.endsWith(".class")){
            fileNames.add(file.getPath());
        }
        if(file.isDirectory()){
            String[] innerFiles = file.list();
            for(String innerFile:innerFiles){
                getFileInDic(new File(file,innerFile),fileNames);
            }
        }
    }

    public static void ComputeTransitiveClosure(int [][] matrix){
        int n = matrix.length;
        int[][] beforeMatrix = matrix.clone();
        for(int k = 0 ; k <n; k++){
            for(int i = 0 ; i<n; i++){
                for(int j = 0 ; j<n; j++){
                    if(beforeMatrix[i][j]==1 || (beforeMatrix[i][k]==1 && beforeMatrix[k][j]==1))
                        matrix[i][j] = 1;
                }
            }
            beforeMatrix = matrix.clone();
        }
    }

    public static void outputSelectedMethod(String filePath, HashSet<String> content) throws IOException {
        BufferedWriter bw = new BufferedWriter(new FileWriter(filePath));
        for(String oneLine: content){
            bw.write(oneLine);
            bw.newLine();
        }
        bw.close();
    }

    public static void outputDependencies(String filePath, HashSet<String> dependencyTemp) throws IOException {
        BufferedWriter bw = new BufferedWriter(new FileWriter(filePath));
        bw.write("digraph class{");
        bw.newLine();
        for(String oneDependency: dependencyTemp){
            bw.write("\t");
            bw.write(oneDependency);
            bw.newLine();
        }
        bw.write("}");
        bw.close();
    }

    public static CallGraph getCallGraph(String projectTarget,String scopePath, String exclusionPath) throws IOException, InvalidClassFileException, ClassHierarchyException, CancelException {
        projectTarget = projectTarget.replace('\\','/');
        ClassLoader classLoader = GetFile.class.getClassLoader();
        String projectTargetFile = projectTarget+"/classes";
        String testTargetFile = projectTarget+"/test-classes";
        ArrayList<String> classFiles = new ArrayList<String>();
        ArrayList<String> testClassFiles = new ArrayList<String>();
        getFileInDic(new File(projectTargetFile),classFiles);
        getFileInDic(new File(testTargetFile),testClassFiles);

        //添加原生类
        AnalysisScope scope = AnalysisScopeReader.readJavaScope(scopePath,new File(exclusionPath),classLoader);
        //添加非原生类(ArrayList中的类)
        for(String classFileName: classFiles){
            scope.addClassFileToScope(ClassLoaderReference.Application,new File(classFileName));
        }
        for(String classFileName: testClassFiles){
            scope.addClassFileToScope(ClassLoaderReference.Application,new File(classFileName));
        }
        ClassHierarchy cha = ClassHierarchyFactory.makeWithRoot(scope);
        Iterable<Entrypoint> eps = new AllApplicationEntrypoints(scope,cha);
        CHACallGraph cg = new CHACallGraph(cha);
        cg.init(eps);
        return cg;
    }

    public static ArrayList<String> getChangedInfo(String changeInfoPath, String selectType) throws IOException {
        ArrayList<String> changedInfo = new ArrayList<String>();
        BufferedReader bf = new BufferedReader(new FileReader(new File(changeInfoPath)));
        String line = "";
        while(null!=(line = bf.readLine())){
            if(selectType.equals("-c")){
                String className = line.split(" ")[0];
                changedInfo.add(className);
            }else if(selectType.equals("-m")){
                changedInfo.add(line);
            }
        }
        return changedInfo;
    }

    public static void getCallGraphInfo(CallGraph cg, HashSet<String> classes, HashSet<String>methods,HashSet<String> testMethods){
        for(CGNode node:cg){
            if(node.getMethod() instanceof ShrikeBTMethod){
                ShrikeBTMethod method = (ShrikeBTMethod) node.getMethod();
                if("Application".equals(method.getDeclaringClass().getClassLoader().toString())){

                    //得到节点类名
                    String classInnerName = method.getDeclaringClass().getName().toString();

                    if(!classes.contains(classInnerName)){
                        classes.add(classInnerName);
                    }

                    //得到节点方法名
                    String signature = method.getSignature();
                    if(!methods.contains(classInnerName+" "+signature)){
                        methods.add(classInnerName+" "+signature);
                    }

                    Collection<Annotation> annotations = method.getAnnotations();

                    for(Annotation annotation:annotations) {
                        String annotationString = annotation.toString();
                        String judgeString = annotationString.split(">")[0];
                        if(judgeString.endsWith("Test")){
                            testMethods.add(classInnerName+" "+signature);
                        }
                    }
                }
            }
        }
    }

    public static void setMatrixIndex(HashMap<Integer,String> index, HashMap<String, Integer>indexReverse, HashSet<String> elements){
        int i = 0;
        for(String oneElement: elements){
            indexReverse.put(oneElement,i);
            index.put(i,oneElement);
            i++;
        }
    }

    public static void getDependencyInfo(CallGraph cg, int[][] adjacencyMatrix, HashSet<String> dependencyTemp,
                                         HashSet<String>methods,String selectType, HashMap<String,Integer>indexReverse){
        for(CGNode node:cg){
            if(node.getMethod() instanceof ShrikeBTMethod){
                ShrikeBTMethod method = (ShrikeBTMethod) node.getMethod();
                if("Application".equals(method.getDeclaringClass().getClassLoader().toString())){

                    for (Iterator<CGNode> it = cg.getSuccNodes(node); it.hasNext(); ) {
                        CGNode succ = it.next();
                        if(succ.getMethod() instanceof ShrikeBTMethod){
                            ShrikeBTMethod succMethod = (ShrikeBTMethod) succ.getMethod();
                            if("Application".equals(succMethod.getDeclaringClass().getClassLoader().toString())){
                                String classInnerName = method.getDeclaringClass().getName().toString();
                                String succMethodName = succMethod.getSignature();
                                String succClassName = succMethod.getDeclaringClass().getName().toString();
                                if(methods.contains(succClassName+" "+succMethodName)){
                                    //更改邻接矩阵
                                    int fromIndex = 0;
                                    int toIndex = 0;
                                    if(selectType.equals("-c")){
                                        dependencyTemp.add("\""+succClassName+"\""+" -> "+"\""+
                                                classInnerName+"\";");
                                        fromIndex = indexReverse.get(succClassName);
                                        toIndex = indexReverse.get(classInnerName);
                                    }else if(selectType.equals("-m")){
                                        dependencyTemp.add("\""+succMethodName+"\""+" -> "+"\""+
                                                method.getSignature()+"\";");
                                        fromIndex = indexReverse.get(succClassName+" "+succMethodName);
                                        toIndex = indexReverse.get(classInnerName+" "+method.getSignature());
                                    }
                                    adjacencyMatrix[fromIndex][toIndex] = 1;
                                    //更改类邻接矩阵
                                }
                            }
                        }
                    }
                }
            }
        }
    }
}

