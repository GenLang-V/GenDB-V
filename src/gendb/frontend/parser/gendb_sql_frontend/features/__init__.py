"""Frontend rules of the SQL features beyond the core select-project-join-aggregate fragment, one module each.

The binder (``bind.py``) dispatches sqlglot nodes to them through its explicit tables; the lowerer (``lower.py``)
uses ``cte``; the schema reader (``schema.py``) uses ``constraints``.  Every named refusal they raise is in the one
catalog ``refusal.REASONS``.

* ``avg``, ``minmax``, ``distinct_agg``: AVG, MIN / MAX and ``agg(DISTINCT x)``;
* ``div``, ``like``, ``substring``, ``extract``: division and the scalar functions;
* ``case``: CASE, COALESCE and NULLIF as lazy ``If`` nodes;
* ``subquery``: scalar, IN and ANY / SOME / ALL subqueries;
* ``cte``: non-recursive WITH queries;
* ``params``: typed statement parameters ``$n``;
* ``constraints``: PRIMARY KEY, UNIQUE, FOREIGN KEY and CHECK in the schema DDL.
"""
