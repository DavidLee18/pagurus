void *malloc(unsigned long);
void *calloc(unsigned long, unsigned long);
void *realloc(void *, unsigned long);
void free(void *);
int main(void){int*p=malloc(4);unsigned long a=(unsigned long)p;int*q=(int*)a;free(q);free(p);return 0;}
