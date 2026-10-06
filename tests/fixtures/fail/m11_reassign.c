/* FAIL: reassigning the parameter then freeing it is still summarised consuming. */
void *malloc(unsigned long n);
void free(void *p);

void w(int *p) {
    p = malloc(8);
    free(p);
}

int main(void) {
    int *p = malloc(4);
    w(p);
    free(p);
    return 0;
}
