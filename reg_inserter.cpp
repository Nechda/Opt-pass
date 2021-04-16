#include "llvm/Pass.h"
#include "llvm/IR/Function.h"
#include "llvm/IR/Instructions.h"
#include "llvm/IR/InlineAsm.h"
#include "llvm/IR/IntrinsicInst.h"
#include "llvm/IR/Intrinsics.h"
#include "llvm/Support/raw_ostream.h"

#include "llvm/IR/LegacyPassManager.h"
#include "llvm/Transforms/IPO/PassManagerBuilder.h"

#include "llvm/IR/Dominators.h"
#include "llvm/ADT/GraphTraits.h"
#include "llvm/Support/GenericDomTree.h"

#include <set>
#include <stack>

using namespace llvm;

#define STACK_IMP 0
#define DFS_IMP 1
#define ALGORITHM STACK_IMP

namespace {
struct RegInserter : public FunctionPass {
  static char ID;
  RegInserter() : FunctionPass(ID) {}

  struct Info
  {
    Module* M;
    LLVMContext& C;
    IntegerType* int64_ty;
    PointerType* void_ptr;
    MetadataAsValue* MD;
  };

  void insert_addition_code(Instruction& I, Info& additionData)
  {
    Function *ReadRegister = Intrinsic::getDeclaration(additionData.M, Intrinsic::read_register, additionData.int64_ty);
    auto call = CallInst::Create(ReadRegister->getFunctionType(), ReadRegister, {additionData.MD}, "", &I);
    auto int_cast = new IntToPtrInst(call, PointerType::get(additionData.void_ptr, 0), "", &I);

    auto load = new LoadInst(additionData.void_ptr, int_cast, "", &I);

    auto ptr_cast = new PtrToIntInst(load, additionData.int64_ty , "", &I);
    Function *WriteRegister = Intrinsic::getDeclaration(additionData.M, Intrinsic::write_register, additionData.int64_ty);
    CallInst::Create(WriteRegister->getFunctionType(), WriteRegister, {additionData.MD, ptr_cast}, "", &I);
  }

  #if ALGORITHM == DFS_IMP

  std::set<size_t> declarated_functions;

  bool DFS_based_imp(DomTreeNode* node, Info& additionData){
    bool changed = false;
    std::stack<size_t> saved_functions;

    BasicBlock& BB = *node->getBlock();
      

    for (Instruction& I : BB) {
      if(I.getOpcode() != Instruction::Call) {
        continue;
      }
      auto CI = cast<CallInst>(&I);
      if (CI->getCalledFunction()->isIntrinsic()) {
        continue;
      }

      size_t func_id = reinterpret_cast<size_t>(CI->getCalledFunction());

      //если ранее не была использована такая функция, то выставялем код для работы с регистром
      if(!declarated_functions.count(func_id)){
        insert_addition_code(I,additionData);

        changed = true;
        // добавляем в набор функций, перед которыми уже было обращение к регистру
        declarated_functions.insert(func_id);
        saved_functions.push(func_id);
      }
    }

    for(auto& child : node->children())
      changed |= DFS_based_imp(child, additionData);

    while(!saved_functions.empty())
    {
      declarated_functions.erase(saved_functions.top());
      saved_functions.pop();
    }

    return changed;
  }

  #endif

  #if ALGORITHM == STACK_IMP

  bool stack_based_imp(DominatorTree* dTree, Info& additionData)
  {
    bool changed = false;
    // множество, хранящее набор функций, которые уже опеределены в данной конкретной вершине
    std::set<size_t> declarated_functions;
    // стековая организация определенных функций
    std::stack<size_t> saved_functions;
    // стековая организация количества детей в дереве
    std::stack<size_t> n_child_in_braches;
    // число описанных функций на данном сегменте дерева
    size_t n_declarated_functions = 0;
    saved_functions.push(0);


    //проходимся по дереву доминаторов в порядке DFS
    for(auto node  = GraphTraits<DominatorTree*>::nodes_begin(dTree);
             node != GraphTraits<DominatorTree*>::nodes_end(dTree);
             node ++
    )
    {
      BasicBlock& BB = *node->getBlock();
      

      for (Instruction& I : BB) {
        if(I.getOpcode() != Instruction::Call) {
          continue;
        }
        auto CI = cast<CallInst>(&I);
        if (CI->getCalledFunction()->isIntrinsic()) {
          continue;
        }
        
        // эту переменную будем использовать как
        // уникальный индентификатор для каждой функции
        size_t func_id = reinterpret_cast<size_t>(CI->getCalledFunction());

        //если ранее не была использована такая функция, то вcтавялем код для работы с регистром
        if(!declarated_functions.count(func_id)){
          insert_addition_code(I, additionData);

          changed = true;
          // добавляем в набор функций, перед которыми уже было обращение к регистру
          declarated_functions.insert(func_id);
          // сохраняем порядок вставки в set
          saved_functions.push(func_id);
          n_declarated_functions++;

          // отдельно рассматриваем случай, когда в дереве возникает развилка
          if(node->getNumChildren() > 1)
          {
            n_child_in_braches.push(node->getNumChildren() - 1); // сохраняем количество детей
            saved_functions.push(n_declarated_functions);        // и число функций, которое было описано до ветвления
            n_declarated_functions = 0;                          // обнуляем переменную, для подсчета на каждом `прямом` участке 
          }
        }
      }

      //проверка на то, что мы находимся в листе дерева
      if(!node->getNumChildren()){
        // тут необходимо уменьшить `номер ветви` на последней развилке 
        if(!n_child_in_braches.empty() ? n_child_in_braches.top() : 0)
          n_child_in_braches.top()--;

        // и удалить из set все функции, которые были объявлены на данной ветви в первый раз
        while(n_declarated_functions--){
          size_t should_pop_func = saved_functions.top();
          declarated_functions.erase(should_pop_func);
          saved_functions.pop();
        }
        n_declarated_functions = 0;

        // если мы оказались на последней `ветке` в развилке, то воспринимаем её как продолжение
        // того пути, по которому мы пришли в вершину с ветвлением
        if(!n_child_in_braches.empty() ? !n_child_in_braches.top() : 0){
          n_child_in_braches.pop();
          n_declarated_functions = saved_functions.top();
          saved_functions.pop();
        }
      }
    }
    return changed;
  }

  #endif

  bool runOnFunction(Function &F) override {
    bool changed = false;
    auto& C = F.getContext();
    Info info{
      F.getParent(),
      F.getContext(),
      Type::getInt64Ty(C),
      PointerType::getInt8PtrTy(C, 0),
      MetadataAsValue::get(C, MDNode::get(C, {MDString::get(C, "x28")}))
    };
    #if 0
    auto *M = F.getParent();
    auto &C = F.getContext();
    auto int64_ty = Type::getInt64Ty(C);
    auto void_ptr = PointerType::getInt8PtrTy(C, 0);
    auto MD = MetadataAsValue::get(C, MDNode::get(C, {MDString::get(C, "x28")}));
    #endif
    // Initialize x28 reg
    if (F.getName() == "main") {
      auto &EBB = F.getEntryBlock();
      auto &I = *EBB.getFirstInsertionPt();
      // void *y;
      auto alloca = new AllocaInst(info.void_ptr, 0, "", &I);
      // x28 = &y;
      auto ptr_cast = new PtrToIntInst(alloca, info.int64_ty , "", &I);
      Function *WriteRegister = Intrinsic::getDeclaration(info.M, Intrinsic::write_register, info.int64_ty);
      CallInst::Create(WriteRegister->getFunctionType(), WriteRegister, {info.MD, ptr_cast}, "", &I);
      // y = x;
      Function *ReadRegister = Intrinsic::getDeclaration(info.M, Intrinsic::read_register, info.int64_ty);
      auto call = CallInst::Create(ReadRegister->getFunctionType(), ReadRegister, {info.MD}, "", &I);
      auto int_cast = new IntToPtrInst(call, info.void_ptr, "", &I);
      new StoreInst(int_cast, alloca, &I);
      changed = true;
    }

    DominatorTree* dTree = new DominatorTree(F);

    #if ALGORITHM == STACK_IMP
      changed |= stack_based_imp(dTree, info);
    #elif ALGORITHM == DFS_IMP
      changed |= DFS_based_imp(dTree->getRootNode(), info);
    #endif
    
    delete dTree;
    return changed;
  }
}; // end of struct RegInserter
}  // end of anonymous namespace

char RegInserter::ID = 0;
static RegisterPass<RegInserter> X("reg_inserter", "RegInserter Pass",
                                   false /* Only looks at CFG */,
                                   false /* Analysis Pass */);

static RegisterStandardPasses Y(
    PassManagerBuilder::EP_EarlyAsPossible,
    [](const PassManagerBuilder &Builder,
       legacy::PassManagerBase &PM) { PM.add(new RegInserter()); });
