# z3mcp.py
from mcp.server.fastmcp import FastMCP
from z3 import *

# Create an MCP server
mcp = FastMCP("Z3 Solver")


# Evaluate SMT commands
@mcp.tool()
def eval(command : str) -> str:
    """Evaluate an SMTLIB2 Command using Z3
    Whenever you are faced with a problem that can be formulated as SMTLIB2 constraints
    always use this function to solve the problem.
    """
    return Z3_eval_smtlib2_string(main_ctx().ctx, command)

if __name__ == "__main__":
    mcp.run()
