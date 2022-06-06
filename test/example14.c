#include "verifier.h"

int main() {
  int x = input();
  while (x) {
    x++;
  }
  assert(x == 0);
  return 0;
}
