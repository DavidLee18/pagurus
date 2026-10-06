/* PASS: free, then p = 0, then free(p) is free(NULL) — a defined no-op. */
void *malloc(unsigned long);
void *calloc(unsigned long, unsigned long);
void *realloc(void *, unsigned long);
void free(void *);
int main(void){int*p=malloc(4);free(p);p=0;free(p);return 0;}
