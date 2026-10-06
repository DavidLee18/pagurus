/* FAIL: direct free of the parameter is Always-consume; caller free is DF/UAM. */
void *malloc(unsigned long n);
void free(void *p);

void w(int *p) { free(p); }

int main(void) {
    int *p = malloc(4);
    w(p);
    free(p);
    return 0;
}
