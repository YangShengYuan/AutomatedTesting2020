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
 * @Description select tests according to method/class dependencies
 **/
public class Main {
    /***
     * 取得命令参数和所需文件的路径并执行主方法
     * @param args 命令行输入的参数
     */
    public static void main(String[] args){
        //获取到命令行输入的参数
        String selectType = args[0];//类依赖或方法依赖
        String projectTargetPath = args[1];//待分析项目target目录
        String changeInfoPath = args[2];//待分析项目更改方法列表

        //在idea内运行时scope和exclusion文件的路径
        String scopePath = "src/main/resources/scope.txt";
        String exclusionPath = "src/main/resources/exclusion.txt";

        //打包成jar后scope和exclusion文件的路径
//        String scopePath = "scope.txt";
//        String exclusionPath = "exclusion.txt";

        try {
            //执行主方法，catch异常
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

    /**
     * 进行测试选择的主方法
     * @param selectType -c表示类级别/-m表示方法级别
     * @param projectTargetPath 待分析项目的target目录
     * @param changeInfoPath 待分析项目更改方法的列表
     * @param scopePath wala scope文件路径
     * @param exclusionPath wala exclusion文件路径
     */
    public static void execute(String selectType, String projectTargetPath, String changeInfoPath,String scopePath, String exclusionPath) throws CancelException, ClassHierarchyException, InvalidClassFileException, IOException {
        //根据项目target目录，scope文件和exclusion文件建立调用图cg
        CallGraph cg = getCallGraph(projectTargetPath,scopePath,exclusionPath);

        //按照是类级别还是方法级别，获取修改的类名/方法名存入HashSet changeInfo中
        HashSet<String> changeInfo = getChangedInfo(changeInfoPath,selectType);

        //待测项目中类名、方法名、测试方法名列表
        //类名为包括类型描述符的wala中得到的表示形式
        HashSet<String> classes = new HashSet<String>();
        //方法名为包括类名和方法签名的wala中得到的表示形式
        HashSet<String> methods = new HashSet<String>();
        //测试方法名形式同方法名
        HashSet<String> testMethods = new HashSet<String>();
        //遍历调用图，填充上述三个Hashset
        getCallGraphInfo(cg, classes,methods,testMethods);

        //项目中的类/方法依赖关系可以视为图的数据结构，因此用邻接矩阵来存储该依赖图结构
        // 矩阵中的[i,j]位元素为1或0，为1表示类/方法i的修改会影响到类/方法j
        // 根据测试选择的级别决定了邻接矩阵中存储的是类级别关系还是方法级别关系
        int[][] adjacencyMatrix;
        //邻接矩阵的行号和其所表示的类名/方法名的索引关系，该Map可以通过行号找到对应的类名/方法名
        HashMap<Integer,String> index = new HashMap<Integer, String>();
        //邻接矩阵的行号和其所表示的类名/方法名的逆索引关系，该Map可以通过类名/方法名找到对应的行号
        //同时使用两个HashMap来实现双向索引，提高运行速度
        HashMap<String,Integer> indexReverse = new HashMap<String,Integer>();
        //邻接矩阵的大小
        int matrixCount = 0;
        if(selectType.equals("-c")){//如果是类级别测试用例选择，邻接矩阵大小为项目中类数量
            matrixCount = classes.size();
            setMatrixIndex(index,indexReverse,classes);//填充上述两个索引map
        }else if(selectType.equals("-m")){//如果是方法级别测试用例选择，邻接矩阵大小为项目中方法数量
            matrixCount = methods.size();
            setMatrixIndex(index,indexReverse,methods);//填充上述两个索引map
        }
        adjacencyMatrix = new int[matrixCount][matrixCount];//初始化邻接矩阵

        //存储方法/类的依赖关系的HashSet，该信息用于后续生成代码关系图.dot文件
        HashSet<String> dependencyTemp = new HashSet<String>();
        //再次遍历调用图上的节点，根据图上节点的前驱后继关系来填充邻接矩阵和代码关系HashSet
        getDependencyInfo(cg,adjacencyMatrix,dependencyTemp,methods,selectType,indexReverse);

        //在临界矩阵上计算传递闭包(从而间接调用关系也能被考虑进依赖关系中)
        ComputeTransitiveClosure(adjacencyMatrix);

        //根据是类级还是方法级的测试用例选择来在邻接矩阵上选择出受影响的测试方法
          //记录被选择出的测试方法的HashSet
        HashSet<String> selectedMethods = new HashSet<String>();
        if(selectType.equals("-c")) {//类级
            //根据被修改的类名找到所有被影响的类
            HashSet<String> influencedClasses = new HashSet<String>();//所有被影响的类
            for(String changedClass: changeInfo){//对每个修改的类
                int i = indexReverse.get(changedClass);//得到修改类在邻接矩阵中的索引
                for(int k = 0; k<adjacencyMatrix.length;k++){
                    if(adjacencyMatrix[i][k]==1){//在邻接矩阵中，找到所有该修改类影响的类的索引
                        String influencedClass = index.get(k);//从map中根据修改影响到的类的索引得到被影响类的类名
                        influencedClasses.add(influencedClass);
                    }
                }
            }
            //遍历一遍测试方法，判断该测试方法是否在被影响类中，在则被选中
            for(String method: testMethods){
                if(influencedClasses.contains(method.split(" ")[0])){
                    selectedMethods.add(method);
                }
            }
        }else if(selectType.equals("-m")) {//方法级
            //根据被修改的方法名找到所有被影响的方法
            for(String changedMethod: changeInfo){//对每个修改的方法
                int i = indexReverse.get(changedMethod);//得到修改方法在邻接矩阵中的索引
                for(int k = 0; k<adjacencyMatrix.length;k++){
                    if(adjacencyMatrix[i][k]==1){//在邻接矩阵中，找到所有该修改方法影响的方法的索引
                        String influencedMethod = index.get(k);//从map中根据修改影响到的方法的索引得到被影响方法的方法名
                        //判断该方法是否属于测试方法，是则被选中
                        if(testMethods.contains(influencedMethod)){
                            selectedMethods.add(influencedMethod);
                        }
                    }
                }
            }
        }

        //输出结果到指定文件中，分别输出选中的方法到selection文件，输出依赖关系到dot文件
        if(selectType.equals("-c")){//类级
            outputSelectedMethod("selection-class.txt",selectedMethods);
//            outputDependencies("class-CMD.text",dependencyTemp);
        }else if(selectType.equals("-m")){//方法级
            outputSelectedMethod("selection-method.txt",selectedMethods);
//            outputDependencies("method-CMD.text",dependencyTemp);
        }
    }

    /**
     * 使用wala对项目静态分析建立调用图的方法
     * @param projectTarget 待分析项目的target目录路径
     * @param scopePath wala配置文件中的scope文件，用来生成包含必须的java原生类的分析域
     * @param exclusionPath walap配置文件中的exclusion文件，表示排除在分析域外的不关心的类
     * @return 使用CHA算法建立的CallGraph
     */
    public static CallGraph getCallGraph(String projectTarget,String scopePath, String exclusionPath) throws IOException, InvalidClassFileException, ClassHierarchyException, CancelException {
        //将项目的target路径添加生产代码类路径和测试代码类路径
        String projectTargetFile = projectTarget+File.separator+"classes";
        String testTargetFile = projectTarget+File.separator+"test-classes";

        //classFiles为所有生产类的.class文件的路径，testClassFiles为所有测试类的class文件的路径
        ArrayList<String> classFiles = new ArrayList<String>();
        ArrayList<String> testClassFiles = new ArrayList<String>();
        //调用递归遍历文件夹方法，将class文件路径添加到ArrayList中
        getFileInDic(new File(projectTargetFile),classFiles);
        getFileInDic(new File(testTargetFile),testClassFiles);

        //得到classLoader
        ClassLoader classLoader = Main.class.getClassLoader();
        //生成wala分析域
        AnalysisScope scope = AnalysisScopeReader.readJavaScope(scopePath,new File(exclusionPath),classLoader);
        //添加非原生类(依据生产代码和测试代码的.class文件)
        for(String classFileName: classFiles){
            scope.addClassFileToScope(ClassLoaderReference.Application,new File(classFileName));
        }
        for(String classFileName: testClassFiles){
            scope.addClassFileToScope(ClassLoaderReference.Application,new File(classFileName));
        }

        //建立层次类结构
        ClassHierarchy cha = ClassHierarchyFactory.makeWithRoot(scope);
        //生成进入点
        Iterable<Entrypoint> eps = new AllApplicationEntrypoints(scope,cha);
        //使用CHA算法生成调用图cg并返回
        CHACallGraph cg = new CHACallGraph(cha);
        cg.init(eps);
        return cg;
    }

    /**
     * 递归遍历文件夹，将文件夹中的.class文件的路径加入方法参数中的arrayList中
     * @param file 可能是待遍历文件夹，或一个文件
     * @param fileNames 存放.class文件路径的arrayList
     */
    public static void getFileInDic(File file,ArrayList<String> fileNames){
        //如果文件为.class文件，加入arrayList中
        String fileName = file.getName();
        if(fileName.endsWith(".class")){
            fileNames.add(file.getPath());
        }
        //如果文件为文件夹，那么列出所有文件夹中的文件，然后递归遍历这些文件
        if(file.isDirectory()){
            String[] innerFiles = file.list();
            if (innerFiles != null) {//判断是否文件夹内有文件
                for(String innerFile:innerFiles){
                    getFileInDic(new File(file,innerFile),fileNames);
                }
            }
        }
    }

    /**
     * 按照是类级别还是方法级别，获取修改的类名/方法名存入HashSet中并返回
     * @param changeInfoPath 记录修改类的文件路径
     * @param selectType 代表测试选择级别的参数
     * @return 存储了修改的类/方法名的HashSet
     */
    public static HashSet<String> getChangedInfo(String changeInfoPath, String selectType) throws IOException {
        //存储了修改的类/方法名的HashSet，使用HashSet避免出现重复字段
        HashSet<String> changedInfo = new HashSet<String>();
        //逐行读取记录了修改方法的文件
        BufferedReader bf = new BufferedReader(new FileReader(new File(changeInfoPath)));
        String line = "";
        while(null!=(line = bf.readLine())){
            if(selectType.equals("-c")){//如果测试选择级别为类级，将每一行的类名加入HashSet
                String className = line.split(" ")[0];
                changedInfo.add(className);
            }else if(selectType.equals("-m")){////如果测试选择级别为方法级，将每一行直接加入HashSet
                changedInfo.add(line);
            }
        }
        return changedInfo;
    }

    /**
     * 遍历调用图的节点，填充项目的类名，方法名和测试方法名列表
     * @param cg 项目调用图
     * @param classes 待填充项目类名列表
     * @param methods 待填充项目方法名列表
     * @param testMethods 待填充项目测试方法名列表
     */
    public static void getCallGraphInfo(CallGraph cg, HashSet<String> classes, HashSet<String>methods,HashSet<String> testMethods){
        for(CGNode node:cg){//遍历调用图的每个节点
            if(node.getMethod() instanceof ShrikeBTMethod){//只关心项目中的ShrikeBTMethod方法
                ShrikeBTMethod method = (ShrikeBTMethod) node.getMethod();//得到节点的方法对象
                if("Application".equals(method.getDeclaringClass().getClassLoader().toString())){

                    //得到方法所在类的类名(即类内部表示)
                    String classInnerName = method.getDeclaringClass().getName().toString();
                    //将类名加入项目类名列表
                    classes.add(classInnerName);

                    //得到节点方法名
                    String signature = method.getSignature();
                    //将方法名(包括类名+方法签名)加入项目方法名列表
                    methods.add(classInnerName+" "+signature);

                    //获取该方法的所有注解
                    Collection<Annotation> annotations = method.getAnnotations();

                    //遍历该方法的注解
                    for(Annotation annotation:annotations) {
                        //得到注解的字符串表示
                        String annotationString = annotation.toString();
                        //按照字符>来分割注解(分割后得到的第一个字符串末尾为注解名)
                        String judgeString = annotationString.split(">")[0];
                        if(judgeString.endsWith("Test")){//判断注解名是否是Test,如果是，判定为测试方法，加入测试方法名列表
                            testMethods.add(classInnerName+" "+signature);
                        }
                    }
                }
            }
        }
    }

    /**
     * 填充邻接矩阵的两个索引HashMap(即填充对应的矩阵行号和类名/方法名)
     * @param index 邻接矩阵行号->类名/方法名的索引map
     * @param indexReverse 类名/方法名->邻接矩阵行号的索引map
     * @param elements 根据是类级别还是方法级别的测试用例选择，该HashSet为类名列表/方法名列表
     */
    public static void setMatrixIndex(HashMap<Integer,String> index, HashMap<String, Integer>indexReverse, HashSet<String> elements){
        int i = 0;//邻接矩阵行号，从0开始
        for(String oneElement: elements){
            indexReverse.put(oneElement,i);//填充逆向索引map
            index.put(i,oneElement);//填充索引map
            i++;//下一个行号
        }
    }

    /**
     * 遍历调用图的节点，根据节点的前驱后继关系，填充邻接矩阵和代码关系HashSet
     * @param cg 项目调用图
     * @param adjacencyMatrix 待填充的代码依赖关系的邻接矩阵
     * @param dependencyTemp 待填充的代码关系HashSet
     * @param methods 项目方法名列表
     * @param selectType 测试依赖级别
     * @param indexReverse 邻接矩阵行号->类名/方法名的索引map
     */
    public static void getDependencyInfo(CallGraph cg, int[][] adjacencyMatrix, HashSet<String> dependencyTemp,
                                         HashSet<String>methods,String selectType, HashMap<String,Integer>indexReverse){
        for(CGNode node:cg){//遍历方法节点
            if(node.getMethod() instanceof ShrikeBTMethod){
                ShrikeBTMethod method = (ShrikeBTMethod) node.getMethod();
                if("Application".equals(method.getDeclaringClass().getClassLoader().toString())){
                    //对于每个关心的方法节点，对图上节点的所有后继节点迭代
                    for (Iterator<CGNode> it = cg.getSuccNodes(node); it.hasNext(); ) {
                        CGNode succ = it.next();
                        if(succ.getMethod() instanceof ShrikeBTMethod){
                            ShrikeBTMethod succMethod = (ShrikeBTMethod) succ.getMethod();
                            if("Application".equals(succMethod.getDeclaringClass().getClassLoader().toString())){
                                //如果某个后继节点也是关心的方法节点，获取该后继节点的类名，方法名
                                String classInnerName = method.getDeclaringClass().getName().toString();
                                String succMethodName = succMethod.getSignature();
                                String succClassName = succMethod.getDeclaringClass().getName().toString();
                                if(methods.contains(succClassName+" "+succMethodName)){//判断该后继方法在不在方法列表中(从而确保已被邻接矩阵索引)

                                    //在邻接矩阵中添加代码依赖关系，在依赖关系HashSet中添加依赖关系文本
                                    int fromIndex = 0;//矩阵中关系头节点
                                    int toIndex = 0;  //矩阵中关系尾节点
                                    if(selectType.equals("-c")){//如果是类级别依赖，添加的是图上节点的类名之间的依赖关系
                                        dependencyTemp.add("\""+succClassName+"\""+" -> "+"\""+
                                                classInnerName+"\";");
                                        fromIndex = indexReverse.get(succClassName);//根据map找到节点的类名对应索引
                                        toIndex = indexReverse.get(classInnerName); //根据map找到节点后继节点的类名的对应索引
                                    }else if(selectType.equals("-m")){//如果是方法级别依赖，添加的是图上节点的方法名之间的依赖关系
                                        dependencyTemp.add("\""+succMethodName+"\""+" -> "+"\""+
                                                method.getSignature()+"\";");
                                        fromIndex = indexReverse.get(succClassName+" "+succMethodName);//根据map找到节点的方法名对应索引
                                        toIndex = indexReverse.get(classInnerName+" "+method.getSignature());//根据map找到节点的后继方法的类名对应索引
                                    }
                                    adjacencyMatrix[fromIndex][toIndex] = 1;//邻接矩阵中对应位置为1，表示修改fromIndex节点会影响toIndex节点
                                }
                            }
                        }
                    }
                }
            }
        }
    }

    /**
     * 使用Warshall算法在临界矩阵上计算传递闭包(从而间接调用关系也能被考虑进依赖关系中)
     *    Warshall算法伪代码如下
     *    R0<-A
     *    for(k<-1;k<=n;k++)
     *       for(i<-1;i<=n;i++)
     *          for(j<-1,j<=n;j++)
     *             Rk[i,j] = Rk-1[i,j] or Rk-1[i,k] and Rk-1[k,j]
     *    return Rn
     * @param matrix 邻接矩阵
     */
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

    /**
     * 输出测试方法选择结果到指定文件
     * @param filePath 指定输出的文件路径
     * @param content  输出的内容，一个元素一行
     */
    public static void outputSelectedMethod(String filePath, HashSet<String> content) throws IOException {
        BufferedWriter bw = new BufferedWriter(new FileWriter(filePath));
        for(String oneLine: content){
            bw.write(oneLine);
            bw.newLine();//换行
        }
        bw.close();
    }

    /**
     * 输出依赖文件到.dot文件
     * @param filePath 指定输出的文件路径
     * @param dependencyTemp 输出的内容，一个依赖一行
     */
    public static void outputDependencies(String filePath, HashSet<String> dependencyTemp) throws IOException {
        BufferedWriter bw = new BufferedWriter(new FileWriter(filePath));
        bw.write("digraph class{");
        bw.newLine();
        for(String oneDependency: dependencyTemp){
            bw.write("\t");//每行前输出制表符
            bw.write(oneDependency);
            bw.newLine();//换行
        }
        bw.write("}");
        bw.close();
    }
}

