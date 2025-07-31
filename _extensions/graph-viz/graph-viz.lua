-- Lua filter for embedding D3.js graph visualizations in Quarto

-- Create the extension directory structure first
local function ensure_dir(path)
  os.execute("mkdir -p " .. path)
end

-- Initialize extension
ensure_dir("_extensions/graph-viz")

-- Main shortcode function
function Shortcode(args, kwargs, meta)
  -- Check if this is our graph-viz shortcode
  if args[1] == "graph-viz" then
    local node_id = kwargs["id"] or meta["id"] or "unknown"
    local width = kwargs["width"] or "100%"
    local height = kwargs["height"] or "500"

    -- Generate unique container ID
    local container_id = "graph-viz-" .. node_id .. "-" .. os.time()

    -- Create the HTML with embedded Observable JS
    local html = string.format([[
<div id="%s" class="graph-visualization-container">
  <div class="graph-loading">Loading visualization...</div>
</div>

<script type="module">
import * as d3 from "https://cdn.jsdelivr.net/npm/d3@7/+esm";

// Function to create force-directed graph
function createForceGraph(data, containerId, options = {}) {
  const container = document.getElementById(containerId);
  container.innerHTML = ''; // Clear loading message

  const {
    width = 700,
    height = 500,
    nodeRadius = 8,
    linkDistance = 100,
    chargeStrength = -300
  } = options;

  // Node colors by type
  const nodeColors = {
    'Definition': '#4CAF50',
    'Theorem': '#2196F3',
    'Axiom': '#FF9800',
    'Example': '#9C27B0'
  };

  // Create SVG
  const svg = d3.create("svg")
    .attr("viewBox", [0, 0, width, height])
    .attr("width", width)
    .attr("height", height)
    .style("max-width", "100%%")
    .style("height", "auto");

  // Add zoom
  const g = svg.append("g");

  const zoom = d3.zoom()
    .scaleExtent([0.1, 4])
    .on("zoom", (event) => {
      g.attr("transform", event.transform);
    });

  svg.call(zoom);

  // Arrow markers
  svg.append("defs").append("marker")
    .attr("id", "arrow-" + containerId)
    .attr("viewBox", "0 -5 10 10")
    .attr("refX", 20)
    .attr("refY", 0)
    .attr("markerWidth", 6)
    .attr("markerHeight", 6)
    .attr("orient", "auto")
    .append("path")
    .attr("fill", "#999")
    .attr("d", "M0,-5L10,0L0,5");

  // Force simulation
  const simulation = d3.forceSimulation(data.nodes)
    .force("link", d3.forceLink(data.links).id(d => d.index).distance(linkDistance))
    .force("charge", d3.forceManyBody().strength(chargeStrength))
    .force("center", d3.forceCenter(width / 2, height / 2))
    .force("collision", d3.forceCollide().radius(nodeRadius * 1.5));

  // Links
  const link = g.append("g")
    .selectAll("line")
    .data(data.links)
    .join("line")
    .attr("stroke", "#999")
    .attr("stroke-opacity", 0.6)
    .attr("stroke-width", 1.5)
    .attr("marker-end", `url(#arrow-${containerId})`);

  // Nodes
  const node = g.append("g")
    .selectAll("g")
    .data(data.nodes)
    .join("g")
    .call(d3.drag()
      .on("start", dragstarted)
      .on("drag", dragged)
      .on("end", dragended));

  // Add click handler for navigation
  node
    .on("click", function(event, d) {
      if (d.url) {
        // Navigate to the article in the same tab
        window.location.href = d.url;
      }
    })
    .on("auxclick", function(event, d) {
      // Middle-click or right-click to open in new tab
      if (d.url && event.button === 1) {
        // Middle mouse button
        window.open(d.url, "_blank");
      }
    });

  node.append("circle")
    .attr("r", d => d.is_focus ? nodeRadius * 1.5 : nodeRadius)
    .attr("fill", d => nodeColors[d.type] || "#888")
    .attr("stroke", d => d.is_focus ? "#333" : "#fff")
    .attr("stroke-width", d => d.is_focus ? 3 : 1.5)
    .style("cursor", d => d.url ? "pointer" : "default");

  // Add hover effects for clickable nodes
  node.on("mouseover", function(event, d) {
    if (d.url) {
      d3.select(this).select("circle")
        .style("stroke-width", 3)
        .style("filter", "drop-shadow(0 0 3px rgba(0,0,0,0.3))");
    }
  }).on("mouseout", function(event, d) {
    if (d.url) {
      d3.select(this).select("circle")
        .style("stroke-width", d.is_focus ? 3 : 1.5)
        .style("filter", "none");
    }
  });

  node.append("text")
    .text(d => d.label || d.id)
    .attr("x", 0)
    .attr("y", -nodeRadius - 5)
    .attr("text-anchor", "middle")
    .attr("font-size", "11px")
    .attr("font-family", "system-ui, sans-serif");

  // Add proof status icons
  const proofStatusIcons = {
    'completed': '✅',
    'warnings_present': '⚠️',
    'errors_present': '❌',
    'not_implemented': '📝'
  };

  const proofStatusTooltips = {
    'completed': 'Formal proof completed',
    'warnings_present': 'Formal proof has warnings',
    'errors_present': 'Formal proof has errors',
    'not_implemented': 'Formal proof not implemented'
  };

  node.each(function(d) {
    if (d.proof_status && proofStatusIcons[d.proof_status]) {
      const g = d3.select(this);
      g.append("text")
        .text(proofStatusIcons[d.proof_status])
        .attr("x", nodeRadius * 0.7)
        .attr("y", -nodeRadius * 0.7)
        .attr("font-size", "12px")
        .style("user-select", "none");
    }
  });

  node.append("title")
    .text(d => {
      let title = `${d.type}: ${d.label || d.id}`;
      if (d.proof_status && proofStatusTooltips[d.proof_status]) {
        title += `\n${proofStatusTooltips[d.proof_status]}`;
      }
      if (d.url) {
        title += '\n(Click to view article)';
      }
      return title;
    });

  // Tick function
  simulation.on("tick", () => {
    link
      .attr("x1", d => d.source.x)
      .attr("y1", d => d.source.y)
      .attr("x2", d => d.target.x)
      .attr("y2", d => d.target.y);

    node.attr("transform", d => `translate(${d.x},${d.y})`);
  });

  // Drag functions
  function dragstarted(event) {
    if (!event.active) simulation.alphaTarget(0.3).restart();
    event.subject.fx = event.subject.x;
    event.subject.fy = event.subject.y;
  }

  function dragged(event) {
    event.subject.fx = event.x;
    event.subject.fy = event.y;
  }

  function dragended(event) {
    if (!event.active) simulation.alphaTarget(0);
    event.subject.fx = null;
    event.subject.fy = null;
  }

  // Add to container
  container.appendChild(svg.node());

  // Add stats
  const stats = document.createElement("div");
  stats.className = "graph-stats";
  stats.innerHTML = `
    <p><strong>Graph Statistics:</strong></p>
    <ul>
      <li>Nodes: ${data.metadata.total_nodes}</li>
      <li>Links: ${data.metadata.total_links}</li>
      <li>Neighborhood depth: ${data.metadata.depth || 2}</li>
    </ul>
  `;
  container.appendChild(stats);
}

// Load and render the graph
async function loadAndRenderGraph() {
  try {
    // Calculate relative path based on current location
    const currentPath = window.location.pathname;

    // Check if the path ends with a slash (directory URL)
    const isDirectoryUrl = currentPath.endsWith('/');

    // Check if we're in a GitHub Pages subdirectory (e.g., /ModernMath/)
    const pathParts = currentPath.split('/').filter(p => p);
    let basePath = '';

    // For GitHub Pages with project name subdirectory
    if (window.location.hostname.includes('github.io') && pathParts.length > 0) {
      // The first part is the project name (e.g., 'ModernMath')
      const projectName = pathParts[0];

      // For multilingual sites, we need to account for the language directory
      // Path structure: /ModernMath/en/domain/file.html or /ModernMath/ja/domain/file.html
      // We need to go up to /ModernMath/ to access /ModernMath/output/
      let depthFromProjectRoot;

      // Check if the second part is a language code
      if (pathParts.length > 1 && (pathParts[1] === 'en' || pathParts[1] === 'ja')) {
        // Remove project name and language, count remaining directories
        depthFromProjectRoot = pathParts.slice(2).length;

        // If it's not a directory URL, subtract 1 for the HTML file
        if (!isDirectoryUrl) {
          depthFromProjectRoot -= 1;
        }

        // Add one more level to go up from the language directory
        depthFromProjectRoot += 1;

        // Ensure we have at least depth 1 to go up from language directory
        depthFromProjectRoot = Math.max(1, depthFromProjectRoot);
      } else {
        // Original logic for non-multilingual setup
        depthFromProjectRoot = pathParts.slice(1).length;
        if (!isDirectoryUrl) {
          depthFromProjectRoot -= 1;
        }
        depthFromProjectRoot = Math.max(0, depthFromProjectRoot);
      }

      // Go up to the project root
      basePath = '../'.repeat(depthFromProjectRoot);
    } else {
      // For local development or root deployment
      const depth = (currentPath.match(/\//g) || []).length - 1;
      basePath = '../'.repeat(depth);
    }

    // Detect language from URL path and HTML lang attribute
    let lang = 'en';  // default

    // First try URL path detection
    if (currentPath.includes('/ja/') || currentPath.includes('/ja.html')) {
      lang = 'ja';
    } else if (currentPath.includes('/en/') || currentPath.includes('/en.html')) {
      lang = 'en';
    } else {
      // Fallback to HTML lang attribute if URL doesn't clearly indicate language
      const htmlLang = document.documentElement.lang || document.querySelector('html')?.getAttribute('lang');
      if (htmlLang && htmlLang.startsWith('ja')) {
        lang = 'ja';
      }
    }

    console.log('Detected language:', lang, 'from path:', currentPath);
    console.log('Base path calculated:', basePath);

    const dataUrl = basePath + 'output/d3-data/' + lang + '/%s.json';
    console.log('Fetching data from:', dataUrl);

    const response = await fetch(dataUrl);
    if (!response.ok) {
      throw new Error('Failed to load graph data');
    }
    const data = await response.json();
    createForceGraph(data, '%s', {
      width: %s,
      height: %s
    });
  } catch (error) {
    document.getElementById('%s').innerHTML =
      '<div class="alert alert-warning">Unable to load graph visualization. Please run generate_d3_data.py first.</div>';
  }
}

// Load when DOM is ready
if (document.readyState === 'loading') {
  document.addEventListener('DOMContentLoaded', loadAndRenderGraph);
} else {
  loadAndRenderGraph();
}
</script>

<style>
.graph-visualization-container {
  margin: 2em 0;
  padding: 1em;
  background: #f8f9fa;
  border-radius: 8px;
  border: 1px solid #e9ecef;
}

.graph-visualization-container svg {
  display: block;
  margin: 0 auto;
  background: white;
  border: 1px solid #dee2e6;
  border-radius: 4px;
}

.graph-stats {
  margin-top: 1em;
  padding: 0.5em 1em;
  background: white;
  border-radius: 4px;
  font-size: 0.9em;
}

.graph-stats ul {
  margin: 0.5em 0 0 1em;
  padding: 0;
}

.graph-loading {
  text-align: center;
  padding: 2em;
  color: #6c757d;
}

.alert {
  padding: 12px 20px;
  border-radius: 4px;
  margin: 1em 0;
}

.alert-warning {
  background-color: #fff3cd;
  border: 1px solid #ffeaa7;
  color: #856404;
}
</style>
]], container_id, node_id, container_id,
    tonumber(width) or 700,
    tonumber(height) or 500,
    container_id)

    return pandoc.RawBlock("html", html)
  end

  -- Return empty if not our shortcode
  return pandoc.Null()
end

-- Also handle Div with class .graph-viz
function Div(el)
  if el.classes:includes("graph-viz") then
    local node_id = el.attributes["data-id"] or "unknown"
    local width = el.attributes["data-width"] or "700"
    local height = el.attributes["data-height"] or "500"

    -- Create shortcode args
    local kwargs = {id = node_id, width = width, height = height}

    -- Return the visualization
    return Shortcode({"graph-viz"}, kwargs, {id = node_id})
  end
  return el
end
