
// DO NOT EDIT THIS FILE - it is machine generated -*- c++ -*-

#ifndef __javax_swing_text_DefaultStyledDocument$AttributeUndoableEdit__
#define __javax_swing_text_DefaultStyledDocument$AttributeUndoableEdit__

#pragma interface

#include <javax/swing/undo/AbstractUndoableEdit.h>
extern "Java"
{
  namespace javax
  {
    namespace swing
    {
      namespace text
      {
          class AttributeSet;
          class DefaultStyledDocument$AttributeUndoableEdit;
          class Element;
      }
    }
  }
}

class javax::swing::text::DefaultStyledDocument$AttributeUndoableEdit : public ::javax::swing::undo::AbstractUndoableEdit
{

public:
  DefaultStyledDocument$AttributeUndoableEdit(::javax::swing::text::Element *, ::javax::swing::text::AttributeSet *, jboolean);
  virtual void undo();
  virtual void redo();
public: // actually protected
  ::javax::swing::text::AttributeSet * __attribute__((aligned(__alignof__( ::javax::swing::undo::AbstractUndoableEdit)))) copy;
  ::javax::swing::text::AttributeSet * newAttributes;
  jboolean isReplacing;
  ::javax::swing::text::Element * element;
public:
  static ::java::lang::Class class$;
};

#endif // __javax_swing_text_DefaultStyledDocument$AttributeUndoableEdit__
