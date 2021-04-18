#include "llvm/IR/BasicBlock.h"
#include "llvm/IR/Function.h"
#include "llvm/IR/IRBuilder.h"
#include "llvm/IR/LLVMContext.h"
#include "llvm/IR/Module.h"
#include "llvm/IR/Type.h"
#include "llvm/ExecutionEngine/ExecutionEngine.h"
#include "llvm/ExecutionEngine/GenericValue.h"
#include "llvm/Support/TargetSelect.h"

#include <llvm/IR/LegacyPassManager.h>
#include <llvm/Transforms/Scalar.h>

#include "llvm/IR/Dominators.h"
#include "llvm/ADT/GraphTraits.h"
#include "llvm/Support/GenericDomTree.h"

#include <iostream>
#include <fstream>
#include <string>
#include <vector>
#include <stack>

#include "Opt.h"

using namespace llvm;
using namespace std;

/*
    \brief   Аллокатор для построения графа
    \details Аллокатор для построения графа,
             используется для выделения памяти
             под массивы индексов детей.
*/
struct Allocator
{
    size_t* allocate(int n)
    {
        size_t* ptr = new size_t[n];
        m_memory.push_back({ptr,n});
        return ptr;
    }
    void clean_up()
    {
        for(auto it : m_memory)
            delete[] it.first;
        m_memory.clear();
    }
    private:
    std::vector<std::pair<size_t*, int>> m_memory;
};

/*
    \brief   Валидатор сгенерированного IR
    \details Валидатор проверяет, что для каждой функции
             в ранее был сгенерирован код с обращением 
             к регистру.
           
*/
struct Validator
{
    
    /*
        \brief  Множество, хранящее в себе информацию
                о том, какие функции уже определены.
        \note   Изменяется только функцией verify во
                время проверки IR.
    */
    private:
    std::set<size_t> declarated_functions;

    
    /*
        \brief   Функция рекурсивно проверяет IR.
        \details Функция рекурсивно проверяет, что для
                 каждой функции был сгенерирован код с
                 обращением к регистру.
        \param   [in]  node  Указатель на корень дерева доминаторов
        \return  В случае нахождения ошибок в построении IR возвращается
                 true.
    */
    public:
    bool verify(DomTreeNode* node)
    {
        std::stack<size_t> saved_functions;
        BasicBlock& BB = *node->getBlock();

        bool found_undeclarated_function = false;
        bool was_writing_in_register = false;
        for (Instruction& I : BB)
        {
            if(I.getOpcode() != Instruction::Call)
            {
                was_writing_in_register = false;
                continue;
            }
            auto CI = cast<CallInst>(&I);
            if (CI->getCalledFunction()->isIntrinsic())
            {
                was_writing_in_register = CI->getCalledFunction()->getIntrinsicID() == Intrinsic::write_register;
                continue;
            }

            size_t func_id = reinterpret_cast<size_t>(CI->getCalledFunction());

            if(was_writing_in_register)
            {
                declarated_functions.insert(func_id);
                saved_functions.push(func_id);
                was_writing_in_register = false;
            }
            else
                found_undeclarated_function |= !declarated_functions.count(func_id);
        }

        for(auto& child : node->children())
            found_undeclarated_function |= verify(child);

        while(!saved_functions.empty())
        {
            declarated_functions.erase(saved_functions.top());
            saved_functions.pop();
        }

        return found_undeclarated_function;
    }
};


Allocator node_allocator;


struct ControlFlowGraph
{

    /*
        \brief Структура, реализующая узел в графе
    */
    struct Node
    {
        int n_child;         /* число детей у данного узла */
        size_t* m_child_ids; /* массив с индексами детей, сами узлы лежат в `nodes` */
        Node(int nChilds, size_t* childs = nullptr) :
            n_child(nChilds),
            m_child_ids(childs)
        {
            if(n_child && !childs)
                m_child_ids = node_allocator.allocate(n_child);
        }
        ~Node(){}
    };

    /* набор всех */
    vector<Node*> nodes;

    using FunctionId_t = size_t;
    
    ControlFlowGraph()
    {
        nodes.reserve(2);
        nodes.resize(2);
        nodes[0] = new Node(1);       // entry
        nodes[1] = new Node(0);       // last
        nodes[0]->m_child_ids[0] = 1; // entry -> last
    }

    ~ControlFlowGraph()
    {
        node_allocator.clean_up();
        for(auto& node : nodes)
            delete node;
    }

    /*
        \brief  Функция реализует добавление в граф нового
                узла.
        \param  [in]  index     Индекс узла, после которго следует
                                создать новый узел.
        \param  [in]  isBranch  Флаг, указывающий на то будет добавлен
                                один узел или два.
    */
    void insert_node(int index, bool isBranch)
    {
        if(index < 0 || nodes.size() <= index)
            return;
        
        int nChilds = nodes[index]->n_child; 

        if(isBranch)
        {
            Node* brnch_true  = new Node(nChilds, nodes[index]->m_child_ids);
            Node* brnch_false = new Node(nChilds, nodes[index]->m_child_ids);
            nodes.push_back(brnch_true);
            nodes.push_back(brnch_false);
            nodes[index]->m_child_ids = node_allocator.allocate(2);
            nodes[index]->m_child_ids[0] = nodes.size() - 2;
            nodes[index]->m_child_ids[1] = nodes.size() - 1;
            nodes[index]->n_child = 2;
        }
        else
        {
            Node* new_node  = new Node(nChilds, nodes[index]->m_child_ids);
            nodes.push_back(new_node);
            nodes[index]->m_child_ids = node_allocator.allocate(1);
            nodes[index]->m_child_ids[0] = nodes.size() - 1;
            nodes[index]->n_child = 1;
        }
    }

    /*
        \brief  Функция генерирует dot файл, на основе построенного графа.
        \note   Dot-файл имеет название `CFG.dot`
    */
    void draw()
    {
        fstream file;
        file.open("CFG.dot", fstream::out);
        file << "digraph G{\n";
        file << "node [shape = rectangle]\n";
        for(size_t i = 0; i < nodes.size(); i++)
            for(size_t j = 0; j < nodes[i]->n_child; j++)
                file << "NODE" << i << "->" << "NODE" << nodes[i]->m_child_ids[j] << ";" << std::endl;
        file << "}\n";
        file.close();
    }

    /*
        \brief   Функция тестирует оптимизационный проход.
        \details По передаваемым в функцию правилами строится IR предстваление,
                 над которым выполняется оптимизационный проход. После чего,
                 полученный IR проверяется на корректность валидатором.
        \param   [in]  rules  Массив правил, по которым в граф вставляются функции
    */
    bool evaluate(const std::vector<std::pair<size_t, FunctionId_t>>& rules)
    {
        LLVMContext context;
        IRBuilder<> builder(context);
        Module* module = new Module("Main_module", context);

        /*define i32 main(i32 %0)*/
        FunctionType* funcType = FunctionType::get(builder.getInt32Ty(), {builder.getInt32Ty()}, false);
        Function*     mainFunc = Function::Create(funcType, Function::ExternalLinkage, "main", module);
        BasicBlock*   entryBB  = BasicBlock::Create(context, "entry", mainFunc);
        builder.SetInsertPoint(entryBB);

        /* all branches will use `argc` from function `main` as condition */
        Value* condition = mainFunc->getArg(0);

        /* prepare basic blocks */
        std::vector<BasicBlock*> bb(nodes.size());
        for(int i = 0; i < nodes.size(); i++)
            bb[i] = BasicBlock::Create(context, "BB" + to_string(i), mainFunc);

        /* jumping from entry to first bb in graph */
        builder.CreateBr(bb[0]);

        /* insert functions in blocks */
        FunctionType* externalFunctionType = FunctionType::get(builder.getInt32Ty(), false);
        for(const auto& rule : rules)
        {
            builder.SetInsertPoint(bb[rule.first]);
            FunctionCallee f = module->getOrInsertFunction(
                "function_" + to_string(rule.second),
                externalFunctionType
            );
            builder.CreateCall(f);
        }

        /* insert branches in bb */
        for(int i = 0; i < nodes.size(); i++)
        {
            builder.SetInsertPoint(bb[i]);
            switch(nodes[i]->n_child)
            {
                case 2:
                    builder.CreateCondBr(
                        condition,
                        bb[nodes[i]->m_child_ids[0]],
                        bb[nodes[i]->m_child_ids[1]]
                    );
                    break;
                case 1:
                    builder.CreateBr(bb[nodes[i]->m_child_ids[0]]);
                    break;
                case 0:
                    builder.CreateRet(builder.getInt32(0));
                    break;
            }
        }

        /* do our optimization */
        legacy::FunctionPassManager* TheFPM = new legacy::FunctionPassManager(module);
        TheFPM->add(createRegInserterPass());
        TheFPM->doInitialization();
        TheFPM->run(*mainFunc);
        delete TheFPM;

        /* check validity of reg insreter */
        Validator validator;
        DominatorTree* dTree = new DominatorTree(*mainFunc);
        bool is_error_occur = validator.verify(dTree->getRootNode());
        delete dTree;

        /*
        std::string s;
        raw_string_ostream os(s);
        module->print(os, nullptr);
        os.flush();
        fstream ir_file;
        ir_file.open("t.ll", std::fstream::out);
        ir_file << s << std::endl;;
        ir_file.close();
        */

        delete module;

        return is_error_occur;
    }
};


/*
    \brief  Функция генерирует случайный узел и вставляет его в граф.
    \param  [in]  cgf          Граф, в который требуется добавить узел
    \param  [out] init_config  Строка, в которую записываются действия,
                               произведенные над графом.
*/
void random_insert_node(ControlFlowGraph& cgf, std::string& init_config)
{
    size_t index = rand() % cgf.nodes.size();
    bool isBranch = rand() & 1;
    cgf.insert_node(index, isBranch);

    init_config.append("node ");
    init_config.append(to_string(index) + " ");
    init_config.append(to_string(isBranch) + "\n");
}


/*
    \brief  Функция генерирует случайный набор правил вставки функций в граф.
    \param  [in]  cgf          Граф, для которого генерируются правила
    \param  [out] init_config  Строка, в которую записываются действия,
                               произведенные над графом.
    \return Вектор из набора правил для вставки функций в граф.
*/
auto random_rules(ControlFlowGraph& cgf, std::string& init_config)
{
    vector<pair<size_t, size_t>> rules;
    const size_t n_nodes = cgf.nodes.size();
    for(int i = 0; i < 2 * n_nodes; i++)
    {
        rules.push_back( {rand() % n_nodes, rand() % n_nodes} );
        init_config.append("rule ");
        init_config.append(to_string(rules.back().first) + " ");
        init_config.append(to_string(rules.back().second) + "\n");
    }
    return rules;
}


/*
    \brief  Функция генерирует случайный граф, затем тестирует на нем
            оптимизационный проход.
    \note   В случае провала теста информация о генерации графа записывается
            в файл failed.con.
*/
void test_optimization()
{
    ControlFlowGraph cgf;
    std::string config;
    for(int i = 0; i < (rand() % 5) + 4; i++)
        random_insert_node(cgf, config);
    auto rules = random_rules(cgf, config);
    bool is_error_occur = cgf.evaluate(rules);
    if(!is_error_occur)
        std::cout << "Ok ";
    else
    {
        std::fstream file;
        file.open("failed.con", std::fstream::app);
        file << config << std::endl;
        std::cout << "Test failed. Inital information has wroten in failed.con" << std::endl;
        file.close();
    }
}


int main(int argc, char** argv)
{
    int n_tests = 0;
    switch(argc)
    {
        case 1: n_tests = 2;             break;
        case 2: n_tests = atoi(argv[1]); break;
        default:                         break;
    }     
    srand(time(0));

    for(int i = 0; i < n_tests; i++)
        test_optimization();
    std::cout << std::endl;
    
    return 0;
}