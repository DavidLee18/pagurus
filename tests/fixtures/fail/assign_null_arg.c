/* FAIL: `q = 0` writes `q` unsequenced with the other argument's read of `q`
   (C11 §6.5p2). Previously accepted because null is not a live pointer. */
void free(void *);

void f(int *a, int *b) {
    free(b);
}

int main(void) {
    int *q = 0;
    f(q = 0, q);
    return 0;
}
