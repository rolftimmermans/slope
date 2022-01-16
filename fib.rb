# def fib(n)
#   if n < 2 then
#     1
#   else
#     fib(n - 1) + fib(n - 2)
#   end
# end

# puts fib(36)
# puts fib(36)

def fib(n)
  if n < 2.0 then
    1
  else
    fib(n - 1.0) + fib(n - 2.0)
  end
end

puts fib(36.0)

# puts RubyVM::InstructionSequence.disasm(method(:fib))
