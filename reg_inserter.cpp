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

#include <stack>

using namespace llvm;

namespace {
struct RegInserter : public FunctionPass {
  static char ID;
  RegInserter() : FunctionPass(ID) {}


  bool runOnFunction(Function &F) override {
    bool changed = false;
    auto *M = F.getParent();
    auto &C = F.getContext();
    auto int64_ty = Type::getInt64Ty(C);
    auto void_ptr = PointerType::getInt8PtrTy(C, 0);
    auto MD = MetadataAsValue::get(C, MDNode::get(C, {MDString::get(C, "x28")}));

    // Initialize x28 reg
    if (F.getName() == "main") {
      auto &EBB = F.getEntryBlock();
      auto &I = *EBB.getFirstInsertionPt();
      // void *y;
      auto alloca = new AllocaInst(void_ptr, 0, "", &I);
      // x28 = &y;
      auto ptr_cast = new PtrToIntInst(alloca, int64_ty , "", &I);
      Function *WriteRegister = Intrinsic::getDeclaration(M, Intrinsic::write_register, int64_ty);
      CallInst::Create(WriteRegister->getFunctionType(), WriteRegister, {MD, ptr_cast}, "", &I);
      // y = x;
      Function *ReadRegister = Intrinsic::getDeclaration(M, Intrinsic::read_register, int64_ty);
      auto call = CallInst::Create(ReadRegister->getFunctionType(), ReadRegister, {MD}, "", &I);
      auto int_cast = new IntToPtrInst(call, void_ptr, "", &I);
      new StoreInst(int_cast, alloca, &I);

      changed = true;
    }

    DominatorTree* dTree = new DominatorTree(F);

    // множество, хранящее набор функций, которые уже опеределены в данной конкретной вершине
    std::set<size_t> declarated_functions;
    // стековая организация определенных функций
    std::stack<size_t> saved_functions;
    // стековая организация количества детей в дереве
    std::stack<size_t> n_child_in_braches;
    // число описанных функций на данном сегменте дерева
    size_t n_declarated_functions = 0;
    saved_functions.push(0);

    //проходимся по дереву доминантов в порядке DFS
    for(auto node  = GraphTraits<DominatorTree*>::nodes_begin(dTree);
             node != GraphTraits<DominatorTree*>::nodes_end(dTree);
             node ++
    )
    {
      BasicBlock& BB = *node->getBlock();
      // эту переменную будем использовать как
      // уникальный индентификатор для каждой функции
      

      for (Instruction& I : BB) {
        if(I.getOpcode() != Instruction::Call) {
          continue;
        }
        auto CI = cast<CallInst>(&I);
        if (CI->getCalledFunction()->isIntrinsic()) {
          continue;
        }

        size_t func_type = reinterpret_cast<size_t>(CI->getCalledFunction());

        //если ранее не была использована такая функция, то выставялем код для работы с регистром
        if(!declarated_functions.count(func_type)){
          Function *ReadRegister = Intrinsic::getDeclaration(M, Intrinsic::read_register, int64_ty);
          auto call = CallInst::Create(ReadRegister->getFunctionType(), ReadRegister, {MD}, "", &I);
          auto int_cast = new IntToPtrInst(call, PointerType::get(void_ptr, 0), "", &I);

          auto load = new LoadInst(void_ptr, int_cast, "", &I);

          auto ptr_cast = new PtrToIntInst(load, int64_ty , "", &I);
          Function *WriteRegister = Intrinsic::getDeclaration(M, Intrinsic::write_register, int64_ty);
          CallInst::Create(WriteRegister->getFunctionType(), WriteRegister, {MD, ptr_cast}, "", &I);

          changed = true;
          // добавляем в набор функций, перед которыми уже было обращение к регистру
          declarated_functions.insert(func_type);
          // сохраняем порядок вставки в set
          saved_functions.push(func_type);
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
