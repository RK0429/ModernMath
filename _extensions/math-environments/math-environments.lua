-- math-environments.lua
-- Quarto filter for mathematical environments (theorems, definitions, proofs)

local theoremCounter = 0
local definitionCounter = 0
local lemmaCounter = 0
local propositionCounter = 0
local corollaryCounter = 0
local exampleCounter = 0

-- Helper function to create a theorem-like environment
local function createTheoremEnvironment(el, envType, label, title)
    local counter = 0
    local prefix = ""

    if envType == "theorem" then
        theoremCounter = theoremCounter + 1
        counter = theoremCounter
        prefix = "Theorem"
    elseif envType == "definition" then
        definitionCounter = definitionCounter + 1
        counter = definitionCounter
        prefix = "Definition"
    elseif envType == "lemma" then
        lemmaCounter = lemmaCounter + 1
        counter = lemmaCounter
        prefix = "Lemma"
    elseif envType == "proposition" then
        propositionCounter = propositionCounter + 1
        counter = propositionCounter
        prefix = "Proposition"
    elseif envType == "corollary" then
        corollaryCounter = corollaryCounter + 1
        counter = corollaryCounter
        prefix = "Corollary"
    elseif envType == "example" then
        exampleCounter = exampleCounter + 1
        counter = exampleCounter
        prefix = "Example"
    end

    -- Create the header
    local headerContent = pandoc.Strong(pandoc.Str(prefix .. " " .. counter))
    if title and title ~= "" then
        headerContent = pandoc.Span({headerContent, pandoc.Str(" "), pandoc.Str("(" .. title .. ")")})
    end

    -- Create header with label if provided
    local header
    if label and label ~= "" then
        -- Wrap in a Span with the ID for cross-referencing
        headerContent = pandoc.Span(headerContent, pandoc.Attr(label, {}, {}))
    end
    header = pandoc.Para(headerContent)

    -- Combine header and content
    local content = {header}
    for _, block in ipairs(el.content) do
        table.insert(content, block)
    end

    -- Wrap in a div with appropriate class
    return pandoc.Div(content, pandoc.Attr("", {"math-" .. envType}, {}))
end

-- Helper function to create a proof environment
local function createProofEnvironment(el, label)
    -- Create the proof header
    local headerContent = pandoc.Emph(pandoc.Str("Proof."))

    -- Add label anchor if provided
    if label and label ~= "" then
        headerContent = pandoc.Span(headerContent, pandoc.Attr(label, {}, {}))
    end
    local header = pandoc.Para(headerContent)

    -- Add QED symbol at the end
    local lastBlock = el.content[#el.content]
    if lastBlock and lastBlock.t == "Para" then
        table.insert(lastBlock.content, pandoc.Space())
        table.insert(lastBlock.content, pandoc.Str("□"))
    else
        table.insert(el.content, pandoc.Para(pandoc.Str("□")))
    end

    -- Combine header and content
    local content = {header}
    for _, block in ipairs(el.content) do
        table.insert(content, block)
    end

    -- Wrap in a div with proof class
    return pandoc.Div(content, pandoc.Attr("", {"math-proof"}, {}))
end

-- Main filter function
function Div(el)
    -- Check for theorem-like environments
    if el.classes:includes("theorem") then
        return createTheoremEnvironment(el, "theorem", el.attr.identifier, el.attributes.title)
    elseif el.classes:includes("definition") then
        return createTheoremEnvironment(el, "definition", el.attr.identifier, el.attributes.title)
    elseif el.classes:includes("lemma") then
        return createTheoremEnvironment(el, "lemma", el.attr.identifier, el.attributes.title)
    elseif el.classes:includes("proposition") then
        return createTheoremEnvironment(el, "proposition", el.attr.identifier, el.attributes.title)
    elseif el.classes:includes("corollary") then
        return createTheoremEnvironment(el, "corollary", el.attr.identifier, el.attributes.title)
    elseif el.classes:includes("example") then
        return createTheoremEnvironment(el, "example", el.attr.identifier, el.attributes.title)
    elseif el.classes:includes("proof") then
        return createProofEnvironment(el, el.attr.identifier)
    end

    return el
end

-- Return the filter
return {
    {Div = Div},
    {
        Meta = function(meta)
            -- Ensure the CSS file is included
            if quarto.doc.is_format("html") then
                quarto.doc.add_html_dependency({
                    name = "math-environments",
                    version = "1.0.0",
                    stylesheets = {"math-environments.css"}
                })
            end
            return meta
        end
    }
}
