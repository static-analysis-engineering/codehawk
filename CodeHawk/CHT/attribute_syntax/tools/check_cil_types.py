"""Check where CIL attaches attributes on types (accept/accept_types.c).

usage: python3 check_cil_types.py <accept_types_cdict.xml>
Prints PASS/FAIL lines; exit code 1 if any check fails.
"""
import sys
import xml.etree.ElementTree as ET


def table(root, name):
    t = root.find(".//" + name)
    rows = {}
    for n in (t if t is not None else []):
        a = n.get("a")
        rows[int(n.get("ix"))] = (
            n.get("t", ""), [int(x) for x in a.split(",")] if a else [])
    return rows


def main(path):
    root = ET.parse(path).getroot()
    attribute = table(root, "attribute-table")
    attributes = table(root, "attributes-table")
    compinfo = table(root, "compinfo-table")
    fieldinfo = table(root, "fieldinfo-table")
    typ = table(root, "typ-table")
    typeinfo = table(root, "typeinfo-table")
    varinfo = table(root, "varinfo-table")

    def names(attrs_ix):   # attribute names in an attributes list
        return [attribute[i][0] for i in attributes[attrs_ix][1]]

    def comp(name):        # compinfo args: ckey, isstruct, cattr, fields
        return next(a for (t, a) in compinfo.values() if t == name)

    results = []

    def check(label, cond):
        results.append(cond)
        print(("PASS  " if cond else "FAIL  ") + label)

    check("CIL: struct-keyword attribute on compinfo (s1)",
          "chk_inv" in names(comp("s1")[2]))
    check("CIL: closing-brace attribute on compinfo (s2)",
          "chk_inv" in names(comp("s2")[2]))
    s3fields = [fieldinfo[i] for i in comp("s3")[3:]]
    lenfield = next(a for (t, a) in s3fields if t == "len")
    check("CIL: field attribute on fieldinfo (s3.len)",
          "chk_inv" in names(lenfield[3]))
    s5 = comp("s5")
    check("CIL: redeclaration attribute dropped (s5 cattr empty)",
          names(s5[2]) == [])
    tyix = next(a[0] for (t, a) in typeinfo.values() if t == "chk_inv_s5")
    tyt, tya = typ[tyix]
    check("CIL: typedef carrier on TComp s5 type",
          tyt == "tcomp" and tya[0] == s5[0] and "chk_inv" in names(tya[1]))
    fv = next(a for (t, a) in varinfo.values()
              if t.split(",")[0] == "chk_invariant_s5")
    check("CIL: function carrier on varinfo", "chk_inv" in names(fv[2]))
    # T6: typedef carrier of a typedef of an anonymous struct
    tyix6 = next(a[0] for (t, a) in typeinfo.values() if t == "chk_inv_rec_t")
    t6, a6 = typ[tyix6]
    check("CIL: anonymous-struct typedef carrier on TNamed rec_t",
          t6 == "tnamed,rec_t" and len(a6) > 0 and "chk_inv" in names(a6[0]))
    recix = next(a[0] for (t, a) in typeinfo.values() if t == "rec_t")
    rt, ra = typ[recix]
    anon = next((t, a) for (t, a) in compinfo.values() if a[0] == ra[0])
    check("CIL: rec_t unrolls to a generated anonymous compinfo, no attribute",
          rt == "tcomp" and anon[0].startswith("__anonstruct_rec_t")
          and names(anon[1][2]) == [])
    return all(results)


if __name__ == "__main__":
    sys.exit(0 if main(sys.argv[1]) else 1)
