document.addEventListener("DOMContentLoaded", () => {
    const resolvePrelude = (node) => {
        const table =
            window.bpTexPreludeTable && typeof window.bpTexPreludeTable === "object"
                ? window.bpTexPreludeTable
                : {};
        const preludeId = (node.getAttribute("data-bp-tex-prelude-id") || "").trim();
        if (preludeId && typeof table[preludeId] === "string") {
            return table[preludeId].trim();
        }
        const fallback = (node.getAttribute("data-bp-tex-prelude") || "").trim();
        return fallback;
    };
    const renderMath = (node, displayMode) => {
        const tex = node.textContent || "";
        const prelude = resolvePrelude(node);
        const renderInput = prelude ? `${prelude}\n${tex}` : tex;
        katex.render(renderInput, node, { throwOnError: false, displayMode });
        node.setAttribute("data-bp-math-rendered", "1");
    };
    for (const m of document.querySelectorAll(".bp_math.inline")) {
        if (m.getAttribute("data-bp-math-rendered") === "1") continue;
        renderMath(m, false);
    }
    for (const m of document.querySelectorAll(".bp_math.display")) {
        if (m.getAttribute("data-bp-math-rendered") === "1") continue;
        renderMath(m, true);
    }
});
