import dis

def fib(n):
  if n > 1:
    return fib(n - 1) + fib(n - 2)
  else:
    return 1

print(fib(36))

# dis.dis(fib)

