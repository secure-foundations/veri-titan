import re

class Encoder:
	def __init__(self):
		self.factor_count = 0
		self.polys = []
		self.vars = set()

	def get_new_factor(self):
		var = "k_" + str(self.factor_count)
		self.factor_count += 1
		self.vars.add(var)
		return var

	def get_vars_from_term(self, term):
		terms = re.split('\*| |\+|\(|\)|\-', term)
		for var in terms:
			if var == "":
				continue
			try:
				var = int(var)
			except:
				self.vars.add(var)

	def add_cong(self, left, right, mod):
		factor = self.get_new_factor()
		self.get_vars_from_term(left)
		self.get_vars_from_term(right)
		self.get_vars_from_term(mod)
		poly = f"({left}) - ({right}) - {factor} * {mod}"
		self.polys += [poly]

	def add_eq(self, left, right):
		self.get_vars_from_term(left)
		self.get_vars_from_term(right)
		poly = f"({left}) - ({right})"
		self.polys += [poly]
	
	def add_poly(self, poly):
		self.polys += [poly]

	def print_query(self, goal):
		var = ",".join(self.vars)
		print(f"ring r=integer,({var}),dp;")
		print("ideal I = ")
		polys = ",\n".join(self.polys)
		print(polys + ";")
		print("ideal G = groebner(I);")
		print(f"reduce({goal}, G);")
		print("quit;")

e = Encoder()
e.add_cong("A", "a", "b * b")
e.add_cong("u", "(a + x * y) * fm'", "b * b")
e.add_eq("b * b * A_l", "A + x * Y + u * M")
e.add_cong("fm' * M", "-1", "b * b")
e.add_cong("hm'", "fm'", "b")
e.add_cong("a_0", "a", "b")
e.add_cong("u_0", "(a_0 + x_0 * y_0) * hm'", "b")
e.add_eq("b * A_1", "A + x_0 * Y + u_0 * M")
e.add_cong("A_1", "a_1", "b")
e.add_cong("Y", "y_0", "b")
e.add_cong("Y", "y", "b * b")
e.add_eq("x", "x_0 + x_1 * b")
e.add_cong("u_1", "(a_1 + x_1 * y_0) * hm'", "b")
e.add_eq("b * A_r", "A_1 + x_1 * Y + u_1 * M")
e.add_eq("u", "u_0 + u_1 * b")
e.add_poly("M")

e.print_query("A_l - A_r")
