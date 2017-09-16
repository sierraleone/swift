//===--- SILNode.h - Node base class for SIL --------------------*- C++ -*-===//
//
// This source file is part of the Swift.org open source project
//
// Copyright (c) 2014 - 2017 Apple Inc. and the Swift project authors
// Licensed under Apache License v2.0 with Runtime Library Exception
//
// See https://swift.org/LICENSE.txt for license information
// See https://swift.org/CONTRIBUTORS.txt for the list of Swift project authors
//
//===----------------------------------------------------------------------===//
//
// This file defines the SILNode class.
//
//===----------------------------------------------------------------------===//

#ifndef SWIFT_SIL_SILNODE_H
#define SWIFT_SIL_SILNODE_H

#include "llvm/Support/Compiler.h"
#include "llvm/ADT/DenseMapInfo.h"
#include "swift/Basic/LLVM.h"
#include <type_traits>

namespace swift {

class SILBasicBlock;
class SILFunction;
class SILInstruction;
class SILModule;
class SingleValueInstruction;
class ValueBase;

/// An enumeration which contains values for all the nodes in SILNodes.def.
/// Other enumerators, like ValueKind and SILInstructionind, ultimately
/// take their values from this enumerator.
enum class SILNodeKind {
#define NODE(ID, PARENT) \
  ID,
#define NODE_RANGE(ID, FIRST, LAST) \
  First_##ID = FIRST, \
  Last_##ID = LAST,
#include "swift/SIL/SILNodes.def"
};

enum {
  NumSILNodeKindBits = 8
};
static_assert(unsigned(SILNodeKind::Last_SILNode) < (1 << NumSILNodeKindBits),
              "SILNodeKind fits in NumSILNodeKindBits bits");

/// A common base class of all SIL value and instruction nodes.
///
/// This class appears as a base class of both ValueBase and
/// SILInstruction.  Some classes are subclasses of both.  Therefore,
/// some care must be taken when working directly with SILNode pointers,
/// because a complete SIL node object may have multiple SILNode subobjects:
///
/// - There may have multiple SILNode* values that refer to the same
///   logical node.  Data structures and algorithms that rely on
///   uniqueness of a SILNode* should make sure that they're working
///   with the canonical SILNode*; see getCanonicalSILNodeInObject().
///   DenseMaps and DenseSets of SILNode* will assert this automatically.
///
/// - Do not use builtin C++ casts to downcast a SILNode*.  A static_cast
///   from SILNode* to SILInstruction* only works if the referenced
///   SILNode is the base subobject of the object's SILInstruction
///   subobject.  If the SILNode is actually the base subobject of a
///   ValueBase subobject, the cast will yield a meaningful value.
///   Always use the LLVM casts (cast<>, dyn_cast<>, etc.) instead.
///
/// These precautions only apply to SILNode*.  A SILInstruction* or
/// ValueBase* is still unique in the object.
class alignas(8) SILNode {
protected:
  enum class SILNodeStorageLocation {
    Value,
    Instruction
  };

private:
  const unsigned Kind : NumSILNodeKindBits;
  const unsigned StorageLoc : 1;
  const unsigned IsCanonical : 1;

  // TODO: Pack other things in here.

  SILNodeStorageLocation getStorageLoc() const {
    return SILNodeStorageLocation(StorageLoc);
  }

  const SILNode *getCanonicalSILNodeSlowPath() const;

protected:
  SILNode(SILNodeKind kind, SILNodeStorageLocation storageLoc)
    : Kind(unsigned(kind)),
      StorageLoc(unsigned(storageLoc)),
      IsCanonical(storageLoc == SILNodeStorageLocation::Instruction ||
                  !hasMultipleSILNodes(kind)) {}

public:

  /// Does the given kind of node have multiple SILNode bases?
  static bool hasMultipleSILNodes(SILNodeKind kind) {
    // Currently only SingleValueInstructions.  Note that multi-result
    // instructions shouldn't return true for this.
    return kind >= SILNodeKind::First_SingleValueInstruction &&
           kind <= SILNodeKind::Last_SingleValueInstruction;
  }

  /// Is this SILNode the canonical SILNode subobject in this object?
  bool isCanonicalSILNodeInObject() const {
    return IsCanonical;
  }

  /// Return a pointer to the canonical SILNode subobject in this object.
  SILNode *getCanonicalSILNodeInObject() {
    if (IsCanonical) return this;
    return const_cast<SILNode*>(getCanonicalSILNodeSlowPath());
  }
  const SILNode *getCanonicalSILNodeInObject() const {
    if (IsCanonical) return this;
    return getCanonicalSILNodeSlowPath();
  }

  LLVM_ATTRIBUTE_ALWAYS_INLINE
  SILNodeKind getKind() const {
    return SILNodeKind(Kind);
  }

  /// If this is a SILArgument or a SILInstruction get its parent basic block,
  /// otherwise return null.
  SILBasicBlock *getParentBlock() const;

  /// If this is a SILArgument or a SILInstruction get its parent function,
  /// otherwise return null.
  SILFunction *getFunction() const;

  /// If this is a SILArgument or a SILInstruction get its parent module,
  /// otherwise return null.
  SILModule *getModule() const;

  /// Pretty-print the node.  If the node is an instruction, the output
  /// will be valid SIL assembly; otherwise, it will be an arbitrary
  /// format suitable for debugging.
  void print(raw_ostream &OS) const;
  void dump() const;

  /// Pretty-print the node in context, preceded by its operands (if the
  /// value represents the result of an instruction) and followed by its
  /// users.
  void printInContext(raw_ostream &OS) const;
  void dumpInContext() const;

  // Cast to SingleValueInstruction.  This is an implementation detail
  // of the cast machinery.  At a high level, all you need to know is to
  // never use static_cast to downcast a SILNode.
  SingleValueInstruction *castToSingleValueInstruction();
  const SingleValueInstruction *castToSingleValueInstruction() const {
    return const_cast<SILNode*>(this)->castToSingleValueInstruction();
  }

  static bool classof(const SILNode *node) {
    return true;
  }
};

inline llvm::raw_ostream &operator<<(llvm::raw_ostream &OS,
                                     const SILNode &node) {
  node.print(OS);
  return OS;
}

template <class To> struct cast_sil_node_is_unambiguous {
  // The only ambiguity right now is between the value and instruction
  // nodes on a SingleValueInstruction.
  static constexpr bool value =
    // If the destination type isn't a subclass of ValueBase or
    // SILInstruction, there's no ambiguity.
       (!std::is_base_of<SILInstruction, To>::value &&
        !std::is_base_of<ValueBase, To>::value)

    // If the destination type is a proper subclass of ValueBase
    // that isn't a subclass of SILInstruction, there's no ambiguity.
    || (std::is_base_of<ValueBase, To>::value &&
        !std::is_same<ValueBase, To>::value &&
        !std::is_base_of<SILInstruction, To>::value)

    // If the destination type is a proper subclass of SILInstruction
    // that isn't a subclass of ValueBase, there's no ambiguity.
    || (std::is_base_of<SILInstruction, To>::value &&
        !std::is_same<SILInstruction, To>::value &&
        !std::is_base_of<ValueBase, To>::value);
};

template <class To,
          bool IsSingleValueInstruction =
            std::is_base_of<SingleValueInstruction, To>::value,
          bool IsKnownUnambiguous =
            cast_sil_node_is_unambiguous<To>::value>
struct cast_sil_node;

// If all complete objects of the destination type are known to only
// contain a single node, we can just use a static_cast.
template <class To>
struct cast_sil_node<To, /*single value*/ false, /*unambiguous*/ true> {
  static To *doit(SILNode *node) {
    return &static_cast<To&>(*node);
  }
};

// If we're casting to a subclass of SingleValueInstruction, we don't
// need to dynamically check whether the node is an SVI.  In fact,
// we can't, because the static_cast will be ambiguous.
template <class To>
struct cast_sil_node<To, /*single value*/ true, /*unambiguous*/ false> {
  static To *doit(SILNode *node) {
    auto svi = node->castToSingleValueInstruction();
    return &static_cast<To&>(*svi);
  }
};

// Otherwise, we need to dynamically check which case we're in.
template <class To>
struct cast_sil_node<To, /*single value*/ false, /*unambiguous*/ false> {
  static To *doit(SILNode *node) {
    // If the node isn't dynamically a SingleValueInstruction, then this
    // is indeed the SILNode subobject that's statically observable in To.
    if (!SILNode::hasMultipleSILNodes(node->getKind())) {
      return &static_cast<To&>(*node);
    }

    auto svi = node->castToSingleValueInstruction();
    return &static_cast<To&>(*svi);
  }
};

} // end namespace swift

namespace llvm {

/// Completely take over cast<>'ing from SILNode*.  A static_cast to
/// ValueBase* or SILInstruction* can be quite wrong.
template <class To>
struct cast_convert_val<To, swift::SILNode*, swift::SILNode*> {
  using ret_type = typename cast_retty<To, swift::SILNode*>::ret_type;
  static ret_type doit(swift::SILNode *node) {
    return swift::cast_sil_node<To>::doit(node);
  }
};
template <class To>
struct cast_convert_val<To, const swift::SILNode *, const swift::SILNode *> {
  using ret_type = typename cast_retty<To, const swift::SILNode*>::ret_type;
  static ret_type doit(const swift::SILNode *node) {
    return swift::cast_sil_node<To>::doit(const_cast<swift::SILNode*>(node));
  }
};

// We don't support casting from SILNode references yet.
template <class To, class From>
struct cast_convert_val<To, swift::SILNode, From>;
template <class To, class From>
struct cast_convert_val<To, const swift::SILNode, From>;

/// ValueBase * is always at least eight-byte aligned; make the three tag bits
/// available through PointerLikeTypeTraits.
template<>
class PointerLikeTypeTraits<swift::SILNode *> {
public:
  static inline void *getAsVoidPointer(swift::SILNode *I) {
    return (void*)I;
  }
  static inline swift::SILNode *getFromVoidPointer(void *P) {
    return (swift::SILNode *)P;
  }
  enum { NumLowBitsAvailable = 3 };
};

#ifndef NDEBUG

// Specialize these methods to assert that the operands are the
// canonical nodes.  We only need to do this for SILNode, not at any
// other level in the hierarchy.
template<> bool
DenseMapInfo<swift::SILNode *>::isEqual(const swift::SILNode *lhs,
                                        const swift::SILNode *rhs) {
  assert(lhs == getEmptyKey() || lhs == getTombstoneKey() ||
         lhs->isCanonicalSILNodeInObject());
  assert(rhs == getEmptyKey() || rhs == getTombstoneKey() ||
         rhs->isCanonicalSILNodeInObject());
  return lhs == rhs;
}
template<> bool
DenseMapInfo<const swift::SILNode *>::isEqual(const swift::SILNode *lhs,
                                              const swift::SILNode *rhs) {
  assert(lhs == getEmptyKey() || lhs == getTombstoneKey() ||
         lhs->isCanonicalSILNodeInObject());
  assert(rhs == getEmptyKey() || rhs == getTombstoneKey() ||
         rhs->isCanonicalSILNodeInObject());
  return lhs == rhs;
}

#endif

} // end namespace llvm

#endif
