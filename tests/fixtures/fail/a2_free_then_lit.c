/* FAIL: after a real free, overwriting with (int*)1 is not free(NULL). */
void *malloc(unsigned long n);
void free(void *p);

int main(void) {
    int *p = malloc(4);
    free(p);
    p = (int *)1;
    free(p);
    return 0;
}
