// Math Knowledge Graph D3.js Visualization Component
// This module provides reusable graph visualization functions for Observable JS in Quarto

// Color scheme for different node types
const nodeColors = {
  Definition: "#4CAF50",
  Theorem: "#2196F3",
  Axiom: "#FF9800",
  Example: "#9C27B0",
  Lemma: "#2196F3",
  Proposition: "#2196F3",
  Corollary: "#2196F3",
};

// Node shapes mapping
const nodeShapes = {
  Definition: "rect",
  Theorem: "ellipse",
  Axiom: "diamond",
  Example: "rect",
};

// Create a force-directed graph visualization
export function createForceGraph(data, options = {}) {
  const {
    width = 800,
    height = 600,
    nodeRadius = 8,
    linkDistance = 100,
    chargeStrength = -300,
    centerStrength = 0.1,
  } = options;

  // Create SVG container
  const svg = d3
    .create("svg")
    .attr("viewBox", [0, 0, width, height])
    .attr("width", width)
    .attr("height", height)
    .style("background", "#f8f9fa");

  // Add zoom behavior
  const g = svg.append("g");

  const zoom = d3
    .zoom()
    .extent([
      [0, 0],
      [width, height],
    ])
    .scaleExtent([0.1, 4])
    .on("zoom", (event) => {
      g.attr("transform", event.transform);
    });

  svg.call(zoom);

  // Create arrow markers for directed edges
  svg
    .append("defs")
    .selectAll("marker")
    .data(["arrow"])
    .join("marker")
    .attr("id", (d) => d)
    .attr("viewBox", "0 -5 10 10")
    .attr("refX", 20)
    .attr("refY", 0)
    .attr("markerWidth", 6)
    .attr("markerHeight", 6)
    .attr("orient", "auto")
    .append("path")
    .attr("fill", "#999")
    .attr("d", "M0,-5L10,0L0,5");

  // Create force simulation
  const simulation = d3
    .forceSimulation(data.nodes)
    .force(
      "link",
      d3
        .forceLink(data.links)
        .id((d) => d.index)
        .distance(linkDistance),
    )
    .force("charge", d3.forceManyBody().strength(chargeStrength))
    .force(
      "center",
      d3.forceCenter(width / 2, height / 2).strength(centerStrength),
    )
    .force("collision", d3.forceCollide().radius(nodeRadius * 1.5));

  // Create links
  const link = g
    .append("g")
    .attr("class", "links")
    .selectAll("line")
    .data(data.links)
    .join("line")
    .attr("stroke", "#999")
    .attr("stroke-opacity", 0.6)
    .attr("stroke-width", 1.5)
    .attr("marker-end", "url(#arrow)");

  // Create nodes
  const node = g
    .append("g")
    .attr("class", "nodes")
    .selectAll("g")
    .data(data.nodes)
    .join("g")
    .call(drag(simulation));

  // Add circles for nodes
  const circles = node
    .append("circle")
    .attr("r", (d) => (d.is_focus ? nodeRadius * 1.5 : nodeRadius))
    .attr("fill", (d) => nodeColors[d.type] || "#888")
    .attr("stroke", (d) => (d.is_focus ? "#333" : "#fff"))
    .attr("stroke-width", (d) => (d.is_focus ? 3 : 1.5))
    .style("cursor", (d) => (d.url ? "pointer" : "default"))
    .style("transition", "all 0.3s ease");

  // Add hover effects for clickable nodes
  node
    .on("mouseover", function (event, d) {
      if (d.url) {
        d3.select(this)
          .select("circle")
          .style("stroke-width", 3)
          .style("stroke", "#333")
          .style("filter", "drop-shadow(0 0 3px rgba(0,0,0,0.3))");
      }
    })
    .on("mouseout", function (event, d) {
      if (d.url) {
        d3.select(this)
          .select("circle")
          .style("stroke-width", d.is_focus ? 3 : 1.5)
          .style("stroke", d.is_focus ? "#333" : "#fff")
          .style("filter", "none");
      }
    });

  // Add labels
  node
    .append("text")
    .text((d) => d.label || d.id)
    .attr("x", 0)
    .attr("y", -nodeRadius - 5)
    .attr("text-anchor", "middle")
    .attr("font-size", "12px")
    .attr("font-family", "sans-serif")
    .attr("fill", "#333")
    .style("pointer-events", "none"); // Prevent text from blocking clicks

  // Add tooltips
  node.append("title").text((d) => {
    let tooltip = `${d.type}: ${d.label || d.id}`;
    if (d.url) {
      tooltip += "\n(Click to view article)";
    }
    return tooltip;
  });

  // Add click handler for navigation
  node
    .on("click", function (event, d) {
      if (d.url) {
        // Navigate to the article in the same tab
        window.location.href = d.url;
      }
    })
    .on("auxclick", function (event, d) {
      // Middle-click or right-click to open in new tab
      if (d.url && event.button === 1) {
        // Middle mouse button
        window.open(d.url, "_blank");
      }
    });

  // Update positions on tick
  simulation.on("tick", () => {
    link
      .attr("x1", (d) => d.source.x)
      .attr("y1", (d) => d.source.y)
      .attr("x2", (d) => d.target.x)
      .attr("y2", (d) => d.target.y);

    node.attr("transform", (d) => `translate(${d.x},${d.y})`);
  });

  // Drag behavior
  function drag(simulation) {
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

    return d3
      .drag()
      .on("start", dragstarted)
      .on("drag", dragged)
      .on("end", dragended);
  }

  // Add controls
  const controls = svg
    .append("g")
    .attr("class", "controls")
    .attr("transform", `translate(10, 10)`);

  // Zoom controls
  controls
    .append("rect")
    .attr("x", 0)
    .attr("y", 0)
    .attr("width", 30)
    .attr("height", 30)
    .attr("fill", "#fff")
    .attr("stroke", "#ccc")
    .attr("cursor", "pointer")
    .on("click", () => {
      svg
        .transition()
        .duration(750)
        .call(
          zoom.transform,
          d3.zoomIdentity.translate(width / 2, height / 2).scale(1.5),
        );
    });

  controls
    .append("text")
    .attr("x", 15)
    .attr("y", 20)
    .attr("text-anchor", "middle")
    .attr("font-size", "16px")
    .text("+");

  controls
    .append("rect")
    .attr("x", 35)
    .attr("y", 0)
    .attr("width", 30)
    .attr("height", 30)
    .attr("fill", "#fff")
    .attr("stroke", "#ccc")
    .attr("cursor", "pointer")
    .on("click", () => {
      svg.transition().duration(750).call(zoom.transform, d3.zoomIdentity);
    });

  controls
    .append("text")
    .attr("x", 50)
    .attr("y", 20)
    .attr("text-anchor", "middle")
    .attr("font-size", "16px")
    .text("⟲");

  return svg.node();
}

// Create a hierarchical tree visualization
export function createTreeGraph(data, options = {}) {
  const { width = 800, height = 600, nodeSize = [100, 50] } = options;

  // Convert flat data to hierarchy if needed
  const root = d3
    .stratify()
    .id((d) => d.id)
    .parentId((d) => d.parent)(data.nodes);

  // Create tree layout
  const treeLayout = d3
    .tree()
    .nodeSize(nodeSize)
    .separation((a, b) => (a.parent === b.parent ? 1 : 1.5));

  // Apply layout
  const tree = treeLayout(root);

  // Create SVG
  const svg = d3
    .create("svg")
    .attr("viewBox", [-width / 2, -50, width, height])
    .attr("width", width)
    .attr("height", height);

  // Add links
  svg
    .append("g")
    .attr("fill", "none")
    .attr("stroke", "#555")
    .attr("stroke-opacity", 0.4)
    .attr("stroke-width", 1.5)
    .selectAll("path")
    .data(tree.links())
    .join("path")
    .attr(
      "d",
      d3
        .linkVertical()
        .x((d) => d.x)
        .y((d) => d.y),
    );

  // Add nodes
  const node = svg
    .append("g")
    .selectAll("g")
    .data(tree.descendants())
    .join("g")
    .attr("transform", (d) => `translate(${d.x},${d.y})`);

  node
    .append("circle")
    .attr("fill", (d) => (d.children ? "#555" : "#999"))
    .attr("r", 5);

  node
    .append("text")
    .attr("dy", "0.31em")
    .attr("x", (d) => (d.children ? -10 : 10))
    .attr("text-anchor", (d) => (d.children ? "end" : "start"))
    .text((d) => d.data.label || d.data.id)
    .attr("font-size", "12px");

  return svg.node();
}

// Create a simple stats display
export function createStatsDisplay(data) {
  const stats = data.metadata || {};

  const container = d3
    .create("div")
    .attr("class", "graph-stats")
    .style("padding", "10px")
    .style("background", "#f0f0f0")
    .style("border-radius", "5px")
    .style("margin", "10px 0");

  container.append("h4").text("Graph Statistics").style("margin", "0 0 10px 0");

  const list = container
    .append("ul")
    .style("list-style", "none")
    .style("padding", "0")
    .style("margin", "0");

  list.append("li").text(`Nodes: ${stats.total_nodes || data.nodes.length}`);

  list.append("li").text(`Edges: ${stats.total_links || data.links.length}`);

  if (stats.depth) {
    list.append("li").text(`Depth: ${stats.depth}`);
  }

  return container.node();
}

// Export for use in Observable
export default {
  createForceGraph,
  createTreeGraph,
  createStatsDisplay,
  nodeColors,
  nodeShapes,
};
