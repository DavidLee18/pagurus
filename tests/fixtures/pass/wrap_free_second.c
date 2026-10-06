void *malloc(unsigned long);
void *calloc(unsigned long, unsigned long);
void *realloc(void *, unsigned long);
void free(void *);
void fs(void*a,void*b){free(b);}
int main(void){int*p=malloc(4);int*q=malloc(4);fs(p,q);free(p);return 0;}
