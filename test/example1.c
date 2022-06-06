#include "verifier.h"

int main() {
  int x = input();
  assume(x > 1);
  assert(x > 10);
  return 0;
}
