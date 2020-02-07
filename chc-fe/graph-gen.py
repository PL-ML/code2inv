# Testing Z3 API endpoints

from z3 import *
from chc_tools.chctools.horndb import HornClauseDb, load_horn_db_from_file
import re
import sys

def find_inv_fn(db: HornClauseDb):
    inv_fun = []
    for rule in db.get_rules():
        head_name = rule.head().decl().name()
        
        for pred in rule.body():
            pred_name = pred.decl().name()
            if pred_name == head_name:
                inv_fun.append((pred_name, [ str(x)[:str(x).rfind("_")] for x in pred.children() ]))
                # print([type(x) for x in pred.children()])
    return inv_fun

class CHCGraphNode:
    def __init__(self):
        self.id = None
        self.type = ""
        self.value = ""
        self.lval = []
        self.rval = []
        self.args = []

    def to_string(self, indent = ""):
        node_str = ""
        if self.id is not None:
            node_str += indent + self.id + "- " + self.type + ": " + self.value + "\n"
        else:
            node_str += indent + self.type + ": " + self.value + "\n"
        indent += "\t"
        if len(self.lval) > 0:
            for t in self.lval:
                node_str += t.to_string(indent) + "\n"
        if len(self.rval) > 0:
            for t in self.rval:
                node_str += t.to_string(indent) + "\n"
        if len(self.args) > 0:
            for t in self.args:
                node_str += t.to_string(indent) + "\n"
        return node_str

    def to_json (self, indent = ""):
        json_str = ""

        if self.id is not None:
            json_str += indent + '"' + self.id + '": {\n'
            indent += '\t'
        json_str += indent + '"' + self.type + '": "' + self.value + '"'

        if len(self.lval) > 0:
            assert len(self.lval) == 1
            json_str += ',\n' + indent + '"lval": {\n'
            indent += "\t"
            json_str += self.lval[0].to_json(indent) + "\n"
            indent = indent[:-1]
            json_str += indent + "}"

        if len(self.rval) > 0:
            json_str += ',\n' + indent + '"rval": {\n'
            indent += "\t"

            if len(self.rval) == 1:
                json_str += self.rval[0].to_json(indent) + "\n"
            else:
                for rval_idx in range(len(self.rval)):
                    if rval_idx > 0:
                        json_str += ',\n'
                    json_str += indent + '"arg' + str(rval_idx) + '": {\n'
                    json_str += self.rval[rval_idx].to_json(indent + "\t")
                    json_str += "\n" + indent + "}"
                json_str += '\n'
            indent = indent[:-1]
            json_str += indent + "}"

        if len(self.args) > 0:
            for arg_idx in range(len(self.args)):
                json_str += ',\n'
                json_str += indent + '"arg' + str(arg_idx) + '": {\n'
                json_str += self.args[arg_idx].to_json(indent + "\t")
                json_str += "\n" + indent + "}"

        if self.id is not None:
            json_str += "\n" + indent[:-1] + "}"

        return json_str


class CHCGraph:
    def __init__(self):
        self.num_nodes = 0
        self.nodes = []
        self.control_flow = []

    def add_invariant_node(self, inv_function):
        inv_fn_name = inv_function[0][0]
        inv_fn_args = inv_function[0][1]

        node = CHCGraphNode()
        self.num_nodes += 1
        node.id = str(self.num_nodes)
        node.type = "cmd"
        node.value = inv_fn_name

        for idx in range(len(inv_fn_args)):
            self.num_nodes += 1
            var_node = CHCGraphNode()
            var_node.id = str(self.num_nodes)
            var_node.type = "Var"
            var_node.value = "V" + str(idx)
            self.nodes.append(var_node)
            flow = (node.id, var_node.id)
            if flow not in self.control_flow:
                self.control_flow.append(flow)
        return node

    def add_quantified_node(self, quant_expr: QuantifierRef):
        node = CHCGraphNode()
        self.num_nodes += 1
        node.id = str(self.num_nodes)
        node.type = "cmd"
        node.value = "ForAll"
        # add var nodes
        var_node_mapping = {}
        for var_idx in range(quant_expr.num_vars()):
            self.num_nodes += 1
            var_node = CHCGraphNode()
            var_node.id = str(self.num_nodes)
            var_node.type = "QVar"
            var_node.value = quant_expr.var_name(var_idx)
            var_node_mapping[var_idx] = var_node.id
            self.nodes.append(var_node)
            flow = (node.id, var_node.id)
            if flow not in self.control_flow:
                self.control_flow.append(flow)
        if quant_expr.body().decl().name() == "Implies":
            body_node, _, _ = self.add_rule_nodes(quant_expr.body().children()[0], var_node_mapping, quant_expr, {}, {})
            # self.nodes.append(body_node)
            flow = (node.id, body_node.id)
            if flow not in self.control_flow:
                self.control_flow.append(flow)
            head_node, _, _ = self.add_rule_nodes(quant_expr.body().children()[1], var_node_mapping, quant_expr, {}, {})
            self.nodes.append(head_node)
            flow = (node.id, head_node.id)
            if flow not in self.control_flow:
                self.control_flow.append(flow)
        else:
            body_node, _, _ = self.add_rule_nodes(quant_expr.body(), var_node_mapping, quant_expr, {}, {})
            # self.nodes.append(body_node)
            flow = (node.id, body_node.id)
            if flow not in self.control_flow:
                self.control_flow.append(flow)
        return node

    
    def add_rule_nodes(self, expr: ExprRef, var_node_mapping = {}, quant_expr = None, const_mapping = {}, cmd_mapping = {}):
        # print(expr)
        # print(const_mapping)
        # print(cmd_mapping)
        node = CHCGraphNode()
        # self.num_nodes += 1
        # node.id = str(self.num_nodes)
        # print(expr)
        # print(quant_expr)
        if len(expr.children()) == 0:
            if "Var" in str(expr):
                # the expr is a variable
                # node.type = "Var"
                # node.value = quant_expr.var_name(int(re.search("Var\((.*)\)", str(expr)).group(1)))
                node = None
                var_idx = int(re.search("Var\((.*)\)", str(expr)).group(1))
                var_node_id = var_node_mapping[var_idx]
                for n in self.nodes:
                    if n.id == var_node_id:
                        node = n
                        break
                if node is None:
                    raise Exception("Variable not found")
            elif type(expr) == IntNumRef:
                if str(expr) not in const_mapping:
                    node.type = "Const"
                    node.value = str(expr)
                    self.num_nodes += 1
                    node.id = str(self.num_nodes)
                    const_mapping[str(expr)] = node.id
                    self.nodes.append(node)
                else:
                    node_id = const_mapping[str(expr)]
                    node = None
                    for n in self.nodes:
                        if n.id == node_id:
                            node = n
                            break
                    if node is None:
                        raise Exception("Const not found")
            elif str(expr) in ("True", "False"):
                node.type = "cmd"
                self.num_nodes += 1
                node.id = str(self.num_nodes)
                if str(expr) == "True":
                    node.value = "true"
                elif str(expr) == "False":
                    node.value = "false"
                if node.value in cmd_mapping:
                    node_id = cmd_mapping[node.value]
                    node = None
                    for n in self.nodes:
                        if node_id == n.id:
                            node = n
                            break
                    if node is None:
                        raise Exception("Could not find cmd node")
                else:
                    cmd_mapping[node.value] = node.id
                    self.nodes.append(node)
            else:
                node.type = "cmd"
                self.num_nodes += 1
                node.id = str(self.num_nodes)
                node.value = str(expr)
                if node.value in cmd_mapping:
                    node_id = cmd_mapping[node.value]
                    node = None
                    for n in self.nodes:
                        if node_id == n.id:
                            node = n
                            break
                    if node is None:
                        raise Exception("Could not find cmd node")
                else:
                    cmd_mapping[node.value] = node.id
                    self.nodes.append(node)
        else:
            # if str(expr.decl()) in ("<", "<=", ">", ">=", "==", "=", "+", "-", "/", "*", "mod"):
            #     # node is an operator
            #     node.type = "OP"
            #     node.value = str(expr.decl())
            #     for child in expr.children():
            #         node.args.append(self.add_rule_nodes(child, var_node_mapping, quant_expr, True))
            #         # self.control_flow.append((node.id, node.args[-1].id))
            # else:
            #     node.type = "cmd"
            #     node.value = str(expr.decl())
            #     if str(expr.decl()) in ("And", "Or", "Implies") and not nested:
            #         for child in expr.children():
            #             child_node = self.add_rule_nodes(child, var_node_mapping, quant_expr)
            #             self.nodes.append(child_node)
            #             self.control_flow.append((node.id, child_node.id))
            #     else:
            #         for child in expr.children():
            #             node.rval.append(self.add_rule_nodes(child, var_node_mapping, quant_expr, True))
            cmd_str = str(expr.decl())
            if cmd_str not in cmd_mapping:
                node.type = "cmd"
                node.value = str(expr.decl())
                self.num_nodes += 1
                node.id = str(self.num_nodes)
                cmd_mapping[cmd_str] = node.id
                self.nodes.append(node)
                for child in expr.children():
                    child_node, const_mapping, cmd_mapping = self.add_rule_nodes(child, var_node_mapping, quant_expr, const_mapping, cmd_mapping)
                    if child_node.type == "Var" or child_node.type == "QVar" or child_node.type == "Const" or child_node.type == "cmd":
                        pass
                    else:
                        self.nodes.append(child_node)
                    flow = (node.id, child_node.id)
                    if flow not in self.control_flow:
                        self.control_flow.append(flow)
            else:
                node = None
                node_id = cmd_mapping[cmd_str]
                for n in self.nodes:
                    if node_id == n.id:
                        node = n
                        break
                if node is None:
                    raise Exception("Could not find cmd node")
                
                for child in expr.children():
                    child_node, const_mapping, cmd_mapping = self.add_rule_nodes(child, var_node_mapping, quant_expr, const_mapping, cmd_mapping)
                    if child_node.type == "Var" or child_node.type == "QVar" or child_node.type == "Const" or child_node.type == "cmd":
                        pass
                    else:
                        self.nodes.append(child_node)
                    flow = (node.id, child_node.id)
                    if flow not in self.control_flow:
                        self.control_flow.append(flow)
        # print(cmd_mapping)
        # print(const_mapping)
        return node, const_mapping, cmd_mapping

    def add_query_node(self, expr : ExprRef):
        node = CHCGraphNode()
        self.num_nodes += 1
        node.id = str(self.num_nodes)
        node.type = "cmd"
        node.value = "Assert"
        node.rval.append(CHCGraphNode())
        node.rval[0].type = "cmd"
        node.rval[0].value = "Not"
        node.rval[0].rval.append(CHCGraphNode())
        # generalize the following line
        node.rval[0].rval[0].value = str(expr)
        node.rval[0].rval[0].type = "cmd"
        return node

    def build_graph(self, fp: Fixedpoint, queries):
        db = HornClauseDb()
        db.load_from_fp(fp, queries)
        inv_fn = find_inv_fn(db)
        self.num_nodes += 1
        entry_node = CHCGraphNode()
        entry_node.type = "cmd"
        entry_node.value = "SKIP"
        entry_node.id = "ENTRY"
        self.nodes.append(entry_node)
        for rule in fp.get_rules():
            # print("HERE")
            # print(rule)
            if type(rule) == QuantifierRef:
                rule_node = self.add_quantified_node(rule)
                self.nodes.append(rule_node)
            else:
                # print(rule)
                rule_node, _, _ = self.add_rule_nodes(rule, {}, None, {}, {})
            # print(rule_node.to_string())
            self.control_flow.append((entry_node.id, rule_node.id))
        for q in queries:
            query_node = self.add_query_node(q)
            self.nodes.append(query_node)
            self.control_flow.append((entry_node.id, query_node.id))
        inv_node = self.add_invariant_node(inv_fn)
        self.nodes.append(inv_node)
        self.control_flow.append((entry_node.id, inv_node.id))
        self.control_flow.sort(key=lambda x : x[0])

    def to_string(self):
        graph_str = ""
        graph_str += "NODES:\n"
        for node in self.nodes:
            graph_str += node.to_string() + "\n"
        graph_str += "\n\nFLOW:\n"
        for flow in self.control_flow:
            graph_str += str(flow) + "\n"
        return graph_str

    def to_json(self):
        json_str = "{\n\t\"nodes\": {\n"
        indent = "\t\t"
        for node_idx in range(len(self.nodes)):
            if node_idx > 0:
                json_str += ',\n'
            json_str += self.nodes[node_idx].to_json(indent)
        json_str += '\n\t},\n\t\"control-flow\": [\n'
        for flow_idx in range(len(self.control_flow)):
            if flow_idx > 0:
                json_str += ',\n'
            json_str += '\t\t["' + self.control_flow[flow_idx][0] + '", "' + self.control_flow[flow_idx][1] + '"]'
        json_str += '\n\t]\n}'
        return json_str


if len(sys.argv) != 2:
    print("Usage: python graph-gen.py <chc-file>")
    exit(1)
fp = Fixedpoint()
smt = fp.parse_file(sys.argv[1])

g = CHCGraph()
g.build_graph(fp, smt)
print(g.to_json())

# for rule in fp.get_rules():
#     if type(rule) == QuantifierRef and len(rule.body().children()) == 2:
#         print(rule.body().children()[1])



# print(fp.get_rules()[7])
# print("{\n\t\"cmd\": \"chc\",\n\t\"rval\" : {\n\t\t\"arg0\" : {")
# print("\t\t\t\"cmd\": \"rules\",\n\t\t\t\"rval\" : {")
# for rule_idx in range(len(fp.get_rules())):
#     # print("AST OF A RULE\n\n\n\n")
#     # print(rule, type(rule))
#     # print("\t\t\t\t\"arg" + str(rule_idx) + "\": {")
#     rule = fp.get_rules()[rule_idx]
#     print(rule)
#     if type(rule) == QuantifierRef:
#         print(rule.body().decl())
#         print(rule.body().children()[0])
#         print("IMPLIES")
#         print(rule.body().children()[1])
#         # print(printAST(rule.body(), rule, "\t\t\t\t\t"))
#     else:
#         pass
        # print("RULE", rule, "TYPE", type(rule))
        # print("\t\t\t \"cmd\": \"" + str(rule) + "\"")
        # print(printAST(rule, None, "\t\t\t\t\t"))
    # print("\t\t\t\t}", end="")
    # if rule_idx < len(fp.get_rules()) - 1:
    #     print(",")
    # else:
    #     print()
# print("\t\t\t}")
# print("\t\t},")
# print("\t\t\"arg1\" : {")
# print("\t\t\t\"cmd\": \"queries\",\n\t\t\t\"rval\" : {")
# for query_idx in range(len(smt)):
#     print("\t\t\t\t\"arg" + str(query_idx) + "\": {")
#     print(printAST(smt[query_idx], None, "\t\t\t\t\t"))
#     print("\t\t\t\t}", end="")
#     if rule_idx < len(smt) - 1:
#         print(",")
#     else:
#         print()
# print("\t\t\t}")
# print("\t\t}")
# print("\t}\n}")
