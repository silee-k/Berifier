#include "verifier.h"

int main() {
  int x = input();
  int y = input();
  assert(x * 42 / 42 == x + y - y);
  return 0;
}
