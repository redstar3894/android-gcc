// { dg-do assemble  }
// 981203 bkoz
// g++/15800  - test

struct panama {
  panama();
  panama(panama &);
  panama& operator=(panama&); // { dg-message "candidates" }
};

extern panama dig();

void foo() {
   panama obj;
   obj = dig(); // { dg-error "no match" }
}

