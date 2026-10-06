void *malloc(unsigned long);
void *calloc(unsigned long, unsigned long);
void *realloc(void *, unsigned long);
void free(void *);
void sink(void*p){void*q=p;free(q);}
int main(void){int*p=malloc(4);sink(p);free(p);return 0;}
